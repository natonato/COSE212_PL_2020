type exp =
  | NUM of int | TRUE | FALSE | UNIT
  | VAR of id
  | ADD of exp * exp
  | SUB of exp * exp
  | MUL of exp * exp
  | DIV of exp * exp
  | EQUAL of exp * exp
  | LESS of exp * exp
  | NOT of exp
  | SEQ of exp * exp                 (* sequence *)
  | IF of exp * exp * exp            (* if-then-else *)
  | WHILE of exp * exp               (* while loop *)
  | LETV of id * exp * exp           (* variable binding *)
  | LETF of id * id list * exp * exp (* procedure binding *)
  | CALLV of id * exp list           (* call by value *)
  | CALLR of id * id list            (* call by referenece *)
  | RECORD of (id * exp) list        (* record construction *)
  | FIELD of exp * id                (* access record field *)
  | ASSIGN of id * exp               (* assgin to variable *)
  | ASSIGNF of exp * id * exp        (* assign to record field *)
  | WRITE of exp
and id = string

type loc = int
type value =
| Num of int
| Bool of bool
| Unit
| Record of record 
and record = (id * loc) list
type memory = (loc * value) list
type env = binding list
and binding = LocBind of id * loc | ProcBind of id * proc
and proc = id list * exp * env

(********************************)
(*     Handling environment     *)
(********************************)

let rec lookup_loc_env : id -> env -> loc
= fun x env ->
  match env with
  | [] -> raise(Failure ("Variable "^x^" is not included in environment"))
  | hd::tl ->
    begin match hd with
    | LocBind (id,l) -> if(x=id) then l else lookup_loc_env x tl
    | ProcBind _ -> lookup_loc_env x tl
    end

let rec lookup_proc_env : id -> env -> proc
= fun x env ->
  match env with
  | [] -> raise(Failure ("Variable "^x^" is not included in environment"))
  | hd::tl ->
    begin match hd with
    | LocBind _ -> lookup_proc_env x tl
    | ProcBind (id,binding) -> if (x=id) then binding else lookup_proc_env x tl
    end

let extend_env : binding -> env -> env
= fun e env -> e::env

let empty_env = []


(***************************)
(*     Handling memory     *)
(***************************)

let rec lookup_mem : loc -> memory -> value
= fun l mem ->
  match mem with
  | [] -> raise(Failure ("location "^(string_of_int l)^" is not included in memory"))
  | (loc,v)::tl -> if(l=loc) then v else lookup_mem l tl

let extend_mem : (loc * value) -> memory -> memory
= fun (l,v) mem -> (l,v)::mem

let empty_mem = []

(***************************)
(*     Handling record     *)
(***************************)

let rec lookup_record : id -> record -> loc
= fun id record -> 
  match record with
    | [] -> raise(Failure ("field "^ id ^" is not included in record"))
    | (x,l)::tl -> if(id=x) then l else lookup_record id tl


let extend_record : (id * loc) -> record -> record
= fun (x,l) record -> (x,l)::record

let empty_record = []

(***************************)

let counter = ref 0
let new_location () = counter:=!counter+1;!counter

exception NotImplemented
exception UndefinedSemantics

let rec list_fold2 : ('a -> 'b -> 'c -> 'c)-> 'a list -> 'b list -> 'c -> 'c
= fun func l1 l2 acc ->
  match (l1,l2) with
  | ([],[]) -> acc
  | (hd1::tl1,hd2::tl2) -> list_fold2 func tl1 tl2 (func hd1 hd2 acc)
  | _ -> raise (Failure "two lists have different length")

let rec list_fold : ('a -> 'b -> 'b) -> 'a list -> 'b -> 'b
= fun func l acc ->
  match l with
  | [] -> acc
  | hd::tl -> list_fold func tl (func hd acc)

let value2str : value -> string
= fun v ->
  match v with
  | Num n -> string_of_int n
  | Bool b -> string_of_bool b
  | Unit -> "unit"
  | Record _ -> "record" 

let rec eval_aop : env -> memory -> exp -> exp -> (int -> int -> int) -> (value * memory)
= fun env mem e1 e2 op ->
  let (v1,mem1) = eval env mem e1 in
  let (v2,mem2) = eval env mem1 e2 in
  match (v1,v2) with
  | (Num n1, Num n2) -> (Num (op n1 n2), mem2)
  | _ -> raise (Failure "arithmetic operation type error")

and eval : env -> memory -> exp -> (value * memory) 
=fun env mem e -> 
  match e with
  | WRITE e -> 
    let (v1,mem1) = eval env mem e in
    let _ = print_endline(value2str v1) in
    (v1,mem1)
  | NUM n -> (Num n, mem)
  | TRUE -> (Bool true, mem)
  | FALSE -> (Bool false, mem)
  | UNIT -> (Unit, mem)
  | VAR x -> ((lookup_mem (lookup_loc_env x env) mem), mem)
  | ADD (e1, e2) ->(
	let (v1, mem1) = eval env mem e1 in
		let (v2, mem2) = eval env mem1 e2 in
			(match v1, v2 with
			| Num n1, Num n2 -> (Num(n1+n2), mem2)
			| _-> raise UndefinedSemantics
			)
  )  
  | SUB (e1, e2) ->(
	let (v1, mem1) = eval env mem e1 in
		let (v2, mem2) = eval env mem1 e2 in
			(match v1, v2 with
			| Num n1, Num n2 -> (Num(n1-n2), mem2)
			| _-> raise UndefinedSemantics
			)
  )  
  | MUL (e1, e2) ->(
	let (v1, mem1) = eval env mem e1 in
		let (v2, mem2) = eval env mem1 e2 in
			(match v1, v2 with
			| Num n1, Num n2 -> (Num(n1*n2), mem2)
			| _-> raise UndefinedSemantics
			)
  )  
  | DIV (e1, e2) ->(
	let (v1, mem1) = eval env mem e1 in
		let (v2, mem2) = eval env mem1 e2 in
			(match v1, v2 with
			| Num n1, Num n2 -> (Num(n1/n2), mem2)
			| _-> raise UndefinedSemantics
			)
  )  
  | EQUAL (e1, e2) ->(
	let (v1, mem1) = eval env mem e1 in
		let (v2, mem2) = eval env mem1 e2 in
			(match v1, v2 with
			| Num n1, Num n2 ->((if n1=n2 then Bool true else Bool false), mem2)
			| Bool n1, Bool n2 ->((if n1=n2 then Bool true else Bool false), mem2)
			| Unit, Unit ->(Bool true, mem2)
			| _-> raise UndefinedSemantics
			)
  )  
  | LESS (e1, e2) ->(
	let (v1, mem1) = eval env mem e1 in
		let (v2, mem2) = eval env mem1 e2 in
			(match v1, v2 with
			| Num n1, Num n2 ->((if n1<n2 then Bool true else Bool false), mem2)
			| _-> raise UndefinedSemantics
			)
  )  
  | NOT e ->(
	match eval env mem e with
	| (Bool b, mem) -> (Bool (not b), mem)
	| _ -> raise UndefinedSemantics
  )
  | SEQ (e1,e2) -> let (v1, mem1) = eval env mem e1 in eval env mem1 e2
  | IF (e1,e2,e3) ->(
	match eval env mem e1 with
	| (Bool b, mem2) -> if b then eval env mem2 e2 else eval env mem2 e3
	| _ -> raise UndefinedSemantics
  )
  | WHILE (e1, e2) ->(
	match eval env mem e1 with
	| (Bool true, mem1) ->(
		match eval env mem1 e2 with
		| (v2, mem2) -> eval env mem2 (WHILE (e1, e2))
		| _ -> raise UndefinedSemantics
	)
	| (Bool false, mem1) -> (Unit, mem1)
	| _ -> raise UndefinedSemantics
  )
  | LETV (x1, e1, e2) ->(
	let (v1, mem1) = eval env mem e1 in
		let (v2, mem2) = eval (extend_env (LocBind(x1, !counter)) env) (extend_mem (new_location(), v1) mem1) e2 in
			(v2, mem2)
  )
  | LETF (x1, xl1, e1, e2) ->(
	let (v1, mem1) = eval (extend_env (ProcBind(x1, (xl1, e1, env))) env) mem e2 in
		(v1, mem1)
  )
  | CALLV (f1, vl1) ->(
	let (xl1, e1, env1) = lookup_proc_env f1 env in
		let func = fun x1 v1 (env_origin, envf, memf) ->(
			let (v2, mem2) = eval env_origin memf v1 in
				let l = new_location() in
				let env2 = extend_env (LocBind(x1, l)) envf in
					let mem3 = extend_mem (l, v2) mem2 in
						(env_origin, env2, mem3)
		) in
		let (env, envf, memf) = list_fold2 func xl1 vl1 (env, env1, mem) in
			let (v', mem') = eval (extend_env (ProcBind(f1, (xl1, e1, env))) envf) memf e1 in
				(v', mem')
  )
  | CALLR (f1, xl1) ->(
	let (xl2, e1, env1) = lookup_proc_env f1 env in
	let func = fun x1 x2 (env_origin, envf) ->(
		let l = lookup_loc_env x1 env_origin in
			let env3 = extend_env(LocBind(x2, l)) envf in
				(env_origin, env3)
	)in
	let (env, envf) = list_fold2 func xl1 xl2 (env, env1) in
		let (v', mem') = eval (extend_env (ProcBind(f1, (xl2, e1, env))) envf) mem e1 in
			(v', mem')
  )
  | RECORD l1 ->(
	match l1 with
	| (x1, e1)::t ->(
		let func = fun (x1, e1) (reclist, env, mem) ->(
			let (v2, mem2) = eval env mem e1 in
				let l = new_location() in
				(((x1, l)::reclist), env, (extend_mem (l, v2) mem2))
			)in
			let (reclist, env, mem2) = list_fold func l1 ([], env, mem) in
			(Record reclist, mem2)
	)
	| [] -> (Unit, mem)
	| _ -> raise UndefinedSemantics
  )
  | FIELD (e1, x1) ->(
	let (v1, mem1) = eval env mem e1 in
	match v1 with
	| Record r1 -> (
		match lookup_record x1 r1 with
		| l1 ->(
			match lookup_mem l1 mem1 with
			| v2 -> (v2, mem1)
			| _ -> raise UndefinedSemantics
		)
		| _ -> raise UndefinedSemantics
		)		
	| _ -> raise UndefinedSemantics
	)
  | ASSIGN (x1, e1) -> (
	match eval env mem e1 with
	| (v1, mem1) -> (v1, extend_mem((lookup_loc_env x1 env),v1) mem1)
	| _ -> raise UndefinedSemantics
  )
  | ASSIGNF (e1, x1, e2)-> (
	let (v1, mem1) = eval env mem e1 in
	match v1 with
	| Record r1 ->(
		match lookup_record x1 r1 with
		| l1 -> (
			match eval env mem1 e2 with
			| (v2, mem2) -> (v2, extend_mem(l1, v2) mem2)
			| _ -> raise UndefinedSemantics
		)
		| _ -> raise UndefinedSemantics
	)
	| _ -> raise UndefinedSemantics
  )
  | _ -> raise NotImplemented (* TODO *)

let runb : exp -> value 
=fun exp -> let (v, _) = eval empty_env empty_mem exp in v;;
