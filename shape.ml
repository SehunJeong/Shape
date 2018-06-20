type a = Ptr of p | Int of int | Add of a * a | Nil
and  p = Var of var | Cdr of var
and  b = True | False | Not of b | And of b * b | Equal of a * a | IsNil of p
and  stmt = Assign of p * a | Skip | Seq of stmt list | If of b * stmt * stmt | While of b * stmt | Malloc of p
and var = string


(* CFG *)
type lstmt = LAssign of int * p * a | LSkip of int | LSeq of lstmt list | LIf of int * b * lstmt * lstmt | LWhile of int * b * lstmt | LMalloc of int * p
(* type lstmt = Assign of p * a | Skip | Bool of b | Malloc of p *)
(*
Example program:
malloc t1;
t1.cdr := Nil;
malloc t2;
t2.cdr := t1;
malloc t3;
t3.cdr := t2;
x := t3;
t1 := Nil;
t2 := Nil;
t3 := Nil;
y := Nil;
while (not is-nil(x)) do
  (z:=y; y:=x; x:=x.cdr; y.cdr:=z);
z:=nil
*)
let example_pgm = 
  Seq [
    Malloc (Var "t1");
  ]
let pgm =
    Seq [
      Malloc (Var "t1");
      Assign (Cdr "t1", Nil);
      Malloc (Var "t2");
      Assign (Cdr "t2", Ptr (Var "t1"));
      Malloc (Var "t3");
      Assign (Cdr "t3", Ptr (Var "t2"));
      Assign (Var "x", Ptr (Var "t3"));
      Assign (Var "t1", Nil);
      Assign (Var "t2", Nil);
      Assign (Var "t3", Nil);
      Assign (Var "y", Nil);
      While (Not (IsNil (Var "x")),
        Seq [
          Assign (Var "z", Ptr (Var "y"));
          Assign (Var "y", Ptr (Var "x"));
          Assign (Var "x", Ptr (Cdr "x"));
          Assign (Cdr "y", Ptr (Var "z"));
        ]
      );
      Assign (Var "z", Nil)
    ]

let analysis stmt = 0 (* Placeholder *)

let label_ref = ref 0

let make_label () =
  label_ref := !label_ref + 1;
  !label_ref

let labelof : lstmt -> int
=fun labeled_stmt ->
  match labeled_stmt with
  | LAssign (l, _, _) -> l
  | LIf (l, _, _, _) -> l
  | LMalloc (l, _) -> l
  | LSkip (l) -> l
  | LWhile (l, _, _) -> l
  | LSeq lst -> -1

let rec string_of_ptr : p -> string
=fun pe ->
  match pe with
  | Var v -> v
  | Cdr v -> v ^ ".cdr"

let rec string_of_ae : a -> string
=fun ae ->
  match ae with
  | Ptr p -> "*" ^ (string_of_ptr p)
  | Int i -> string_of_int i
  | Add (a1, a2) -> (string_of_ae a1) ^ "+" ^ (string_of_ae a2)
  | Nil -> "Nil"

let rec string_of_bool : b -> string
=fun be ->
  match be with
  | True -> "True"
  | False -> "False"
  | Not b -> "!(" ^ (string_of_bool b) ^ ")"
  | And (b1, b2) -> (string_of_bool b1) ^ " && " ^ (string_of_bool b2)
  | Equal (a1, a2) -> (string_of_ae a1) ^ " == " ^ (string_of_ae a2)
  | IsNil p -> (string_of_ptr p) ^ " == Nil"

let rec string_of_stmt : stmt -> string
=fun s ->
  match s with
  | Seq sl -> String.concat "\n" (BatList.map (fun s -> string_of_stmt s) sl)
  | Assign (p, a) -> (string_of_ptr p) ^ " = " ^ (string_of_ae a)
  | Skip -> "Skip"
  | If (b, s1, s2) -> "If " ^ (string_of_bool b) ^ "{" ^ (string_of_stmt s1) ^ "}" ^ " Else {" ^ (string_of_stmt s2) ^ "}"
  | While (b, s) -> "While " ^ (string_of_bool b) ^ " {" ^ (string_of_stmt s) ^ "}"
  | Malloc p -> "Malloc " ^ (string_of_ptr p)
(*
type lstmt = int * Assign of p * a | int * Skip | Seq of lstmt list | If of (int * b) * lstmt * lstmt | While of (int * b) * lstmt | int * Malloc of p
*)
let rec get_labeled_stmt : stmt -> lstmt
=fun s ->
  match s with
  | Seq sl -> LSeq (BatList.map (fun s -> get_labeled_stmt s) sl)
  | Assign (p, a) -> 
    let new_label = make_label() in
    LAssign (new_label, p, a)
  | Skip ->
    let new_label = make_label() in
    LSkip (new_label)
  | If (b, s1, s2) ->
    let new_label = make_label() in
    LIf (new_label, b, get_labeled_stmt s1, get_labeled_stmt s2)
  | While (b, s1) ->
    let new_label = make_label() in
    LWhile (new_label, b, get_labeled_stmt s1)
  | Malloc p ->
    let new_label = make_label() in
    LMalloc (new_label, p)


let rec string_of_lstmt : lstmt -> string
=fun ls ->
  match ls with
  | LSeq sl -> String.concat "\n" (BatList.map (fun s -> string_of_lstmt s) sl)
  | LAssign (l, p, a) -> 
    Printf.sprintf "%d[%s = %s]" l (string_of_ptr p) (string_of_ae a)
  | LSkip l -> Printf.sprintf "%d[Skip]" l
  | LIf (l, b, s1, s2) -> 
    Printf.sprintf "If %d[%s] {%s} Else {%s}" l (string_of_bool b) (string_of_lstmt s1) (string_of_lstmt s2)
  | LWhile (l, b, s) -> 
    Printf.sprintf "While %d[%s] {%s}" l (string_of_bool b) (string_of_lstmt s)
  | LMalloc (l, p) -> 
    Printf.sprintf "%d[Malloc %s]" l (string_of_ptr p)

let lpgm = get_labeled_stmt pgm
let rec get_label_map : lstmt -> (int, lstmt) BatMap.t -> (int, lstmt) BatMap.t
=fun lpgm oldmap ->
  match lpgm with
  | LSeq sl -> BatList.fold_right (fun ls oldmap-> get_label_map ls oldmap) sl oldmap
  | LAssign (l, p, a) -> BatMap.add l (LAssign (l, p, a)) oldmap
  | LSkip l -> BatMap.add l (LSkip l) oldmap
  | LIf (l, b, s1, s2) -> BatMap.union (BatMap.union (BatMap.add l (LIf (l, b, s1, s2)) oldmap) (get_label_map s1 BatMap.empty)) (get_label_map s2 BatMap.empty)
  | LWhile (l, b, s) -> BatMap.add l (LWhile (l, b, s)) oldmap
  | LMalloc (l, p) -> BatMap.add l (LMalloc (l, p)) oldmap

let lpgm_map = get_label_map lpgm BatMap.empty

let rec init : lstmt -> int
=fun lpgm ->
  match lpgm with
  | LSeq sl -> (match sl with
    | s1::_ -> init s1
    | [] -> -1)
  | LAssign (l, _, _) -> l
  | LSkip l -> l
  | LIf (l, _, _, _) -> l
  | LWhile (l, _, _) -> l
  | LMalloc (l, _) -> l

let rec final : lstmt -> int BatSet.t
=fun lpgm ->
  match lpgm with
  | LSeq sl ->
    final (BatList.last sl)
  | LAssign (l, _, _) -> BatSet.singleton l
  | LSkip l -> BatSet.singleton l
  | LIf (l, _, s1, s2) -> BatSet.union (final s1) (final s2)
  | LWhile (l, _, _) -> BatSet.singleton l
  | LMalloc (l, _) -> BatSet.singleton l

let rec labels : lstmt -> int BatSet.t
=fun lpgm ->
  match lpgm with
  | LSeq sl -> BatList.fold_right (fun s oldset -> BatSet.union oldset (labels s)) sl BatSet.empty
  | LAssign (l, _, _) -> BatSet.singleton l
  | LSkip l -> BatSet.singleton l
  | LIf (l, _, s1, s2) -> BatSet.add l (BatSet.union (final s1) (final s2))
  | LWhile (l, _, s) -> BatSet.add l (labels s)
  | LMalloc (l, _) -> BatSet.singleton l



type edge = (int * int)

let rec flow : lstmt -> edge BatSet.t
=fun lpgm ->
  match lpgm with
  | LAssign _ -> BatSet.empty
  | LSkip _ -> BatSet.empty
  | LSeq sl -> (match sl with
    | s1::s2 -> 
      let flow_s1 = flow s1 in
      let flow_s2 = flow (LSeq s2) in
      let in_flow_to_s2 = BatSet.filter (fun t -> (snd t) <> -1) (BatSet.map (fun l -> (l, init (LSeq s2))) (final s1)) in
      BatSet.union flow_s1 (BatSet.union flow_s2 in_flow_to_s2)
    | [] -> BatSet.empty)
  | LIf (l, _, s1, s2) -> 
    let init_s1_s2 = BatSet.union (BatSet.singleton (l, (init s1))) (BatSet.filter (fun t -> (snd t) <> -1)  (BatSet.singleton (l, (init s2)))) in
    let flow_s1_s2 = BatSet.union (flow s1) (flow s2) in
    BatSet.union init_s1_s2 flow_s1_s2
  | LWhile (l, _, s) -> 
    let flow_s = flow s in
    let l_init_s = BatSet.singleton (l, (init s)) in
    let l'_l = BatSet.map (fun l' -> (l', l)) (final s) in
    BatSet.union flow_s (BatSet.union l_init_s l'_l)
  | LMalloc (l, _) -> BatSet.empty

let rflow : lstmt -> edge BatSet.t
=fun lpgm ->
  BatSet.map (fun f -> (snd f, fst f)) (flow lpgm)

type blocks = LBool of int * b | LAssign of int * p * a | LSkip of int | LMalloc of int * p

let string_of_blocks : blocks -> string
=fun blk ->
  match blk with 
  | LBool (l, b) -> Printf.sprintf "%d[%s]" l (string_of_bool b)
  | LAssign (l, p, a) -> string_of_lstmt (LAssign (l, p, a))
  | LSkip l -> string_of_lstmt (LSkip l)
  | LMalloc (l, p) -> string_of_lstmt (LMalloc (l, p))

let rec blocks : lstmt -> blocks BatSet.t
=fun lpgm ->
  match lpgm with
  | LAssign (l, p, a) -> BatSet.singleton (LAssign (l, p, a))
  | LSkip l -> BatSet.singleton (LSkip l)
  | LSeq sl -> (match sl with 
    | hd::tl -> BatSet.union (blocks hd) (blocks (LSeq tl))
    | [] -> BatSet.empty)
  | LIf (l, b, s1, s2) -> BatSet.union (BatSet.singleton (LBool (l, b))) (BatSet.union (blocks s1) (blocks s2))
  | LWhile (l, b, s) -> BatSet.union (BatSet.singleton (LBool (l, b))) (blocks s)
  | LMalloc (l, p) -> BatSet.singleton (LMalloc (l, p))


type aloc = var BatSet.t
and astate = (var * aloc) BatSet.t
and sel = Cdr of var
and aheap = (aloc * sel * aloc) BatSet.t
and isShared = aloc BatSet.t

let inv1 : aloc -> aloc -> bool
=fun absloc1 absloc2 ->
  BatSet.equal absloc1 absloc2 || (BatSet.equal BatSet.empty (BatSet.intersect absloc1 absloc2))

let inv2 : astate -> bool
=fun abstate ->
  true

let inv3 : aheap -> bool
=fun absheap ->
  true

let aloc_of_heap : aheap -> aloc BatSet.t
=fun absheap ->
  BatSet.fold (fun (al1, _, al2) oldset -> BatSet.add al1 (BatSet.add al2 oldset)) absheap BatSet.empty

let inv4 : isShared -> bool
=fun sharing ->
  true

let inv5 : aheap -> isShared -> bool
=fun absheap sharing ->
  true

type sgraph = (astate * aheap * isShared)
and sg = sgraph BatSet.t

let phi : lstmt -> sg -> sg BatSet.t
=fun l sgraph ->
  BatSet.empty

let f : lstmt -> sg BatSet.t -> sg BatSet.t
=fun l sg ->
  BatSet.fold (fun sgraph oldset -> BatSet.union oldset (phi l sgraph)) sg BatSet.empty

let lstmtof : int -> lstmt
=fun n -> 
  BatMap.find n lpgm_map

let rec shape_in : lstmt -> sg BatSet.t
=fun l ->
  if (labelof l) = init(lpgm) then 
    BatSet.empty 
  else 
    BatSet.fold (fun (l1, l2) oldmap -> if l2 = labelof l then 
                                          BatSet.union oldmap (shape_out (lstmtof l1)) 
                                        else 
                                          BatSet.empty) 
                (flow l) BatSet.empty
and shape_out : lstmt -> sg BatSet.t
=fun l ->
  f l (shape_in l)

(*let worklist *)

let main() = 
  let pgm_flow = flow lpgm in
  BatSet.iter (fun e -> prerr_endline (Printf.sprintf "(%d -> %d)" (fst e) (snd e))) pgm_flow;
  prerr_endline(string_of_int(init(lpgm)));
  prerr_endline(string_of_lstmt lpgm);
  BatSet.iter (fun l -> prerr_endline (string_of_int(l))) (labels lpgm);
  BatSet.iter (fun l -> prerr_endline (string_of_int(l))) (final lpgm);
  BatSet.iter (fun b -> prerr_endline (string_of_blocks b)) (blocks lpgm)
  (*BatList.iter (fun n -> prerr_endline(string_of_int(init(n)))) nodes*)

let _ = main()
