type program = exp
and exp = 
  | UNIT
  | TRUE
  | FALSE
  | CONST of int
  | VAR of var
  | ADD of exp * exp
  | SUB of exp * exp
  | MUL of exp * exp
  | DIV of exp * exp
  | EQUAL of exp * exp
  | LESS of exp * exp
  | NOT of exp
  | NIL
  | CONS of exp * exp      
  | APPEND of exp * exp
  | HEAD of exp
  | TAIL of exp
  | ISNIL of exp
  | IF of exp * exp * exp
  | LET of var * exp * exp
  | LETREC of var * var * exp * exp
  | LETMREC of (var * var * exp) * (var * var * exp) * exp
  | PROC of var * exp
  | CALL of exp * exp
  | PRINT of exp
  | SEQ of exp * exp
and var = string

type value = 
  | Unit 
  | Int of int 
  | Bool of bool 
  | List of value list
  | Procedure of var * exp * env 
  | RecProcedure of var * var * exp * env
  | MRecProcedure of (var * var * exp) * (var * var * exp) * exp
and env = (var * value) list

let rec fold_left : ('a -> 'b -> 'a) -> 'a -> 'b list -> 'a
= fun f accu lst ->
  match lst with
  | [] -> accu
  | hd::tl -> fold_left f (f accu hd) tl

let rec map : ('a -> 'b) -> 'a list -> 'b list
= fun f lst ->
  match lst with
  | [] -> []
  | hd::tl -> (f hd)::(map f tl)

let rec string_of_value v = 
  match v with
  | Int n -> string_of_int n
  | Bool b -> string_of_bool b
  | List lst -> "[" ^ fold_left (fun s x -> s ^ ", " ^ x) "" (map string_of_value lst) ^ "]"
  | _ -> "(functional value)"

exception UndefinedSemantics

let empty_env = []
let extend_env (x,v) e = (x,v)::e
let rec lookup_env x e = 
  match e with
  | [] -> raise (Failure ("variable " ^ x ^ " is not bound in env")) 
  | (y,v)::tl -> if x = y then v else lookup_env x tl

let rec eval : exp -> env -> value
=fun exp env ->
  match exp with
  | PRINT e -> (print_endline (string_of_value (eval e env)); Unit)
  | UNIT -> Unit
  | TRUE -> Bool true
  | FALSE -> Bool false
  | CONST n -> Int n
  | VAR x -> lookup_env x env
  | ADD (e1, e2)->(
	let v1 = eval e1 env in
		let v2 = eval e2 env in
			(match v1, v2 with
			| Int n1, Int n2 -> Int (n1 + n2)
			| _ -> raise UndefinedSemantics
			)
  )
  | SUB (e1, e2)->(
	let v1 = eval e1 env in
		let v2 = eval e2 env in
			(match v1, v2 with
			| Int n1, Int n2 -> Int (n1 - n2)
			| _ -> raise UndefinedSemantics
			)
  )
  | MUL (e1, e2)->(
	let v1 = eval e1 env in
		let v2 = eval e2 env in
			(match v1, v2 with
			| Int n1, Int n2 -> Int (n1 * n2)
			| _ -> raise UndefinedSemantics
			)
  )
  | DIV (e1, e2)->(
	let v1 = eval e1 env in
		let v2 = eval e2 env in
			(match v1, v2 with
			| Int n1, Int n2 -> Int (n1 / n2)
			| _ -> raise UndefinedSemantics
			)
  )
  | EQUAL (e1, e2) ->(
	let v1 = eval e1 env in
		let v2 = eval e2 env in
			(match v1, v2 with
			| Int n1, Int n2 -> if n1=n2 then Bool true else Bool false
			| _ -> raise UndefinedSemantics
			)
  )
  | LESS (e1, e2) ->(
	let v1 = eval e1 env in
		let v2 = eval e2 env in
			(match v1, v2 with
			| Int n1, Int n2 -> if n1<n2 then Bool true else Bool false
			| _ -> raise UndefinedSemantics
			)
  )
  | NOT e1 ->
  (match eval e1 env with
  | Bool true -> Bool false
  | Bool false -> Bool true
  | _ -> raise UndefinedSemantics
  )
  | NIL -> List []
  | CONS (e1, e2)->(
  let v1 = eval e1 env in
	let l1 = eval e2 env in
		(match l1 with
		| List l2 -> List (v1::l2)
		| _ -> raise UndefinedSemantics
		)
  )
  | APPEND (e1, e2) ->(
  let l1 = eval e1 env in
	let l2 = eval e2 env in
		(match l1 with
		| List l1' ->(
			match l2 with
			| List l2' -> List (l1' @ l2')
			| _ -> raise UndefinedSemantics
			)
		| _ -> raise UndefinedSemantics
		)
  )
  | HEAD e1 ->(
  match eval e1 env with
  | List l1 -> (
	match l1 with
	| h::t -> h
	| [] -> raise UndefinedSemantics
	)
  | _ -> raise UndefinedSemantics
  )
  | TAIL e1 ->(
  match eval e1 env with
  | List l1 -> (
	match l1 with
	| h::t -> List (t)
	| [] -> raise UndefinedSemantics
	)
  | _ -> raise UndefinedSemantics
  )
  | ISNIL e1 ->(
	  match eval e1 env with
	  | List l1 ->(
		match l1 with
		| h::t -> Bool false
		| [] -> Bool true 
		)
	  | _ -> raise UndefinedSemantics
  )
  | IF (e1, e2, e3) ->(
	  match eval e1 env with
	  | Bool v -> if v then eval e2 env else eval e3 env
	  | _ -> raise UndefinedSemantics
  )
  | LET (v, e1, e2) ->(
	  let v1 = eval e1 env in
		eval e2 (extend_env (v, v1) env)
  )
  | LETREC (v1, v2, e1, e2) ->(
	  eval e2 (extend_env (v1, RecProcedure(v1, v2, e1, env)) env)
  )
  | LETMREC ((v1_1,v1_2,e1),(v2_1,v2_2,e2),e3)->(
	  eval e3 (extend_env (v2_1, RecProcedure(v2_1,v2_2,e2, env)) (extend_env (v1_1, RecProcedure(v1_1, v1_2, e1, env)) env))
  )
  | PROC (v1, e1) -> Procedure (v1,e1,env)
  | CALL (e1, e2) -> (
	  match eval e1 env with
	  | Procedure(v1,e1,env_funct) ->(
		match eval e2 env with
		| v2 ->eval e1 (extend_env (v1, v2) env_funct)
		| _ -> raise UndefinedSemantics
		)
	  | RecProcedure(v1,v2,e1,env_funct)->(
		match eval e2 env with
		| v3 -> eval e1 (extend_env (v1, RecProcedure(v1,v2,e1,env_funct)) (extend_env (v2,v3) env))        
		| _ -> raise UndefinedSemantics
		)
	  | _ -> raise UndefinedSemantics
  )
  | SEQ (e1, e2) ->(
	  match eval e1 env with
	  | v1 -> eval e2 env
	  | _ -> raise UndefinedSemantics
  )
  

let runml : program -> value
=fun pgm -> eval pgm empty_env
;;