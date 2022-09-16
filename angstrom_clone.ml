module More = struct
  type t = Complete | Incomplete
end

module Exported_state = struct
  type 'a state = Partial of 'a partial | Done of int * 'a | Fail of int * string list * string

  and 'a partial = {
    committed : int;
    continue : Bytes.t -> off:int -> len:int -> More.t -> 'a state;
  }

  let state_to_option = function Done (_, v) -> Some v | Fail _ | Partial _ -> None

  let fail_to_string marks err = String.concat " > " marks ^ ": " ^ err

  let state_to_result = function
    | Done (_, v) -> Ok v
    | Partial _ -> Error "incomplete input"
    | Fail (_, marks, err) -> Error (fail_to_string marks err)
end

module Input = struct
  type t = {
    mutable parser_committed_bytes : int;
    client_committed_bytes : int;
    off : int;
    len : int;
    buffer : Bytes.t;
  }

  let create buffer ~off ~len ~committed_bytes =
    {
      parser_committed_bytes = committed_bytes;
      client_committed_bytes = committed_bytes;
      off;
      len;
      buffer;
    }


  let length t = t.client_committed_bytes + t.len

  let client_committed_bytes t = t.client_committed_bytes

  let parser_committed_bytes t = t.parser_committed_bytes

  let committed_bytes_discrepancy t = t.parser_committed_bytes - t.client_committed_bytes

  let bytes_for_client_to_commit t = committed_bytes_discrepancy t

  let parser_uncommitted_bytes t = t.len - bytes_for_client_to_commit t

  let invariant t =
    assert (parser_committed_bytes t + parser_uncommitted_bytes t = length t);
    assert (parser_committed_bytes t - client_committed_bytes t = bytes_for_client_to_commit t)


  let offset_in_buffer t pos = t.off + pos - t.client_committed_bytes

  let apply t pos len ~f =
    let off = offset_in_buffer t pos in
    f t.buffer ~off ~len


  let unsafe_get_char t pos =
    let off = offset_in_buffer t pos in
    Bytes.get t.buffer off


  let unsafe_get_int32_le t pos =
    let off = offset_in_buffer t pos in
    Bytes.get_int32_le t.buffer off


  let unsafe_get_int32_be t pos =
    let off = offset_in_buffer t pos in
    Bytes.get_int32_be t.buffer off


  let count_while t pos ~f =
    let buffer = t.buffer in
    let off = offset_in_buffer t pos in
    let i = ref off in
    let limit = t.off + t.len in
    while !i < limit && f (Bytes.unsafe_get buffer !i) do
      incr i
    done;
    !i - off


  let commit t pos = t.parser_committed_bytes <- pos
end

module Parser = struct
  module State = struct
    type 'a t =
      | Partial of 'a partial
      | Lazy of 'a t Lazy.t
      | Done of int * 'a
      | Fail of int * string list * string

    and 'a partial = { committed : int; continue : Bytes.t -> off:int -> len:int -> More.t -> 'a t }
  end

  type 'a with_state = Input.t -> int -> More.t -> 'a

  type 'a failure = (string list -> string -> 'a State.t) with_state

  type ('a, 'r) success = ('a -> 'r State.t) with_state

  type 'a t = { run : 'r. ('r failure -> ('a, 'r) success -> 'r State.t) with_state }

  let fail_k input pos _ marks msg =
    State.Fail (pos - Input.client_committed_bytes input, marks, msg)


  let succeed_k input pos _ v = State.Done (pos - Input.client_committed_bytes input, v)

  let rec to_exported_state = function
    | State.Partial { committed; continue } ->
        Exported_state.Partial
          {
            committed;
            continue = (fun bs ~off ~len more -> to_exported_state (continue bs ~off ~len more));
          }
    | State.Done (i, x) -> Exported_state.Done (i, x)
    | State.Fail (i, sl, s) -> Exported_state.Fail (i, sl, s)
    | State.Lazy x -> to_exported_state (Lazy.force x)


  let parse p =
    let input = Input.create Bytes.empty ~committed_bytes:0 ~off:0 ~len:0 in
    to_exported_state (p.run input 0 Incomplete fail_k succeed_k)


  module Monad = struct
    let return v = { run = (fun input pos more _fail succ -> succ input pos more v) }

    let fail msg = { run = (fun input pos more fail _succ -> fail input pos more [] msg) }

    let ( >>= ) p f =
      {
        run =
          (fun input pos more fail succ ->
            let succ' input' pos' more' v = (f v).run input' pos' more' fail succ in
            p.run input pos more fail succ');
      }


    let ( >>| ) p f =
      {
        run =
          (fun input pos more fail succ ->
            let succ' input' pos' more' v = succ input' pos' more' (f v) in
            p.run input pos more fail succ');
      }


    let ( <$> ) f m = m >>| f

    let ( <*> ) f m =
      (* f >>= fun f -> m >>| f *)
      {
        run =
          (fun input pos more fail succ ->
            let succ0 input0 pos0 more0 f =
              let succ1 input1 pos1 more1 m = succ input1 pos1 more1 (f m) in
              m.run input0 pos0 more0 fail succ1
            in
            f.run input pos more fail succ0);
      }


    let lift f m = f <$> m

    let lift2 f m1 m2 =
      {
        run =
          (fun input pos more fail succ ->
            let succ1 input1 pos1 more1 m1 =
              let succ2 input2 pos2 more2 m2 = succ input2 pos2 more2 (f m1 m2) in
              m2.run input1 pos1 more1 fail succ2
            in
            m1.run input pos more fail succ1);
      }


    let ( *> ) a b =
      (* a >>= fun _ -> b *)
      {
        run =
          (fun input pos more fail succ ->
            let succ' input' pos' more' _ = b.run input' pos' more' fail succ in
            a.run input pos more fail succ');
      }


    let ( <* ) a b =
      (* a >>= fun x -> b >>| fun _ -> x *)
      {
        run =
          (fun input pos more fail succ ->
            let succ0 input0 pos0 more0 x =
              let succ1 input1 pos1 more1 _ = succ input1 pos1 more1 x in
              b.run input0 pos0 more0 fail succ1
            in
            a.run input pos more fail succ0);
      }
  end

  module Choice = struct
    let ( <?> ) p mark =
      {
        run =
          (fun input pos more fail succ ->
            let fail' input' pos' more' marks msg = fail input' pos' more' (mark :: marks) msg in
            p.run input pos more fail' succ);
      }


    let ( <|> ) p q =
      {
        run =
          (fun input pos more fail succ ->
            let fail' input' pos' more' marks msg =
              if pos < Input.parser_committed_bytes input' then fail input' pos' more marks msg
              else q.run input' pos more' fail succ
            in
            p.run input pos more fail' succ);
      }
  end
end

module Unbuffered = struct
  include Parser
  include Exported_state

  type more = More.t = Complete | Incomplete
end

include Unbuffered
include Parser.Monad
include Parser.Choice

(* getting input *)

let rec prompt input pos fail succ =
  let parser_uncommitted_bytes = Input.parser_uncommitted_bytes input in
  let parser_committed_bytes = Input.parser_committed_bytes input in
  let continue input ~off ~len (more : More.t) =
    if len < parser_uncommitted_bytes then failwith "prompt: input shrunk!";

    let input = Input.create input ~off ~len ~committed_bytes:parser_committed_bytes in
    if len = parser_uncommitted_bytes then
      match more with
      | Complete -> fail input pos Complete
      | Incomplete -> prompt input pos fail succ
    else succ input pos more
  in
  State.Partial { committed = Input.bytes_for_client_to_commit input; continue }


let demand_input =
  {
    run =
      (fun input pos more fail succ ->
        match (more : More.t) with
        | Complete -> fail input pos more [] "not enough input"
        | Incomplete ->
            let succ' input' pos' more' = succ input' pos' more' ()
            and fail' input' pos' more' = fail input' pos' more' [] "not enough input" in
            prompt input pos fail' succ');
  }


let ensure_suspended n input pos more fail succ =
  let rec go =
    {
      run =
        (fun input' pos' more' fail' succ' ->
          if pos' + n <= Input.length input' then succ' input' pos' more' ()
          else (demand_input *> go).run input' pos' more' fail' succ');
    }
  in
  (demand_input *> go).run input pos more fail succ


let unsafe_apply len ~f =
  {
    run =
      (fun input pos more _fail succ -> succ input (pos + len) more (Input.apply input pos len ~f));
  }


let unsafe_apply_opt len ~f =
  {
    run =
      (fun input pos more fail succ ->
        match Input.apply input pos len ~f with
        | Error e -> fail input pos more [] e
        | Ok x -> succ input (pos + len) more x);
  }
