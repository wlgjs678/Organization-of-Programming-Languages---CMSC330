open MicroCamlTypes
open Utils

exception TypeError of string
exception DeclareError of string
exception DivByZeroError 

(* Provided functions - DO NOT MODIFY *)

(* Adds mapping [x:v] to environment [env] *)
let extend env x v = (x, ref v)::env

(* Returns [v] if [x:v] is a mapping in [env]; uses the
   most recent if multiple mappings for [x] are present *)
let rec lookup env x =
  match env with
  | [] -> raise (DeclareError ("Unbound variable " ^ x))
  | (var, value)::t -> if x = var then !value else lookup t x

(* Creates a placeholder mapping for [x] in [env]; needed
   for handling recursive definitions *)
let extend_tmp env x = (x, ref (Int 0))::env

(* Updates the (most recent) mapping in [env] for [x] to [v] *)
let rec update env x v =
  match env with
  | [] -> raise (DeclareError ("Unbound variable " ^ x))
  | (var, value)::t -> if x = var then (value := v) else update t x v
        
(* Part 1: Evaluating expressions *)

(* Evaluates MicroCaml expression [e] in environment [env],
   returning a value, or throwing an exception on error *)
let rec eval_expr env e =
  match e with
    | Value (v) -> (match v with
      | Int (x) -> Int (x)
      | Bool (x) -> Bool (x)
      | String (x) -> String (x)
      | Closure (x, y, z) -> Closure (x, y, z))
    | ID (x) -> lookup env x
    | Not (x) -> let e1 = eval_expr env x in (match e1 with
      | Bool (e2) -> Bool (not e2)
      | _ -> raise (TypeError "Type error: Not"))
    | Binop (v, e1, e2) -> (match v with
      | Add -> let n1 = eval_expr env e1 in let n2 = eval_expr env e2 in
        (match n1 with
          | Int (a) -> (match n2 with
            | Int (b) -> Int (a+b)
            | _ -> raise (TypeError "Type error: Add: Int"))
          | _ -> raise (TypeError "Type error: Add"))          
      | Sub -> let n1 = eval_expr env e1 in let n2 = eval_expr env e2 in
        (match n1 with
          | Int (a) -> (match n2 with
            | Int (b) -> Int (a-b)
            | _ -> raise (TypeError "Type error: Sub: Int"))
          | _ -> raise (TypeError "Type error: Sub"))
      | Mult -> let n1 = eval_expr env e1 in let n2 = eval_expr env e2 in
        (match n1 with
          | Int (a) -> (match n2 with
            | Int (b) -> Int (a*b)
            | _ -> raise (TypeError "Type error: Mult: Int"))
          | _ -> raise (TypeError "Type error: Mult"))
      | Div -> let n1 = eval_expr env e1 in let n2 = eval_expr env e2 in
        (match n1 with
          | Int (a) -> (match n2 with
            | Int (b) -> if b != 0 then Int (a/b) else raise (DivByZeroError)
            | _ -> raise (TypeError "Type error: Div: Int"))
        | _ -> raise (TypeError "Type error: Div"))
      | Greater -> let n1 = eval_expr env e1 in let n2 = eval_expr env e2 in
        (match n1 with
          | Int (a) -> (match n2 with
            | Int (b) -> Bool (a>b)
            | _ -> raise (TypeError "Type error: Greater: Int"))
          | _ -> raise (TypeError "Type error: Greater"))
      | Less -> let n1 = eval_expr env e1 in let n2 = eval_expr env e2 in
        (match n1 with
          | Int (a) -> (match n2 with
            | Int (b) -> Bool (a<b)
            | _ -> raise (TypeError "Type error: Less: Int"))
          | _ -> raise (TypeError "Type error: Less"))
      | GreaterEqual -> let n1 = eval_expr env e1 in let n2 = eval_expr env e2 in
        (match n1 with
          | Int (a) -> (match n2 with
            | Int (b) -> Bool (a>=b)
            | _ -> raise (TypeError "Type error: GreaterEqual: Int"))
          | _ -> raise (TypeError "Type error: GreaterEqual"))
      | LessEqual -> let n1 = eval_expr env e1 in let n2 = eval_expr env e2 in
        (match n1 with
          | Int (a) -> (match n2 with
            | Int (b) -> Bool (a<=b)
            | _ -> raise (TypeError "Type error: LessEqual: Int"))
          | _ -> raise (TypeError "Type error: LessEqual"))
      | Concat -> let s1 = eval_expr env e1 in let s2 = eval_expr env e2 in
        (match s1 with
          | String (a) -> (match s2 with
            | String (b) -> String (a^b)
            | _ -> raise (TypeError "Type error: Concat: String"))
          | _ -> raise (TypeError "Type error: Concat"))
      | Equal -> let c1 = eval_expr env e1 in let c2 = eval_expr env e2 in
        (match c1 with
          | Int (a) -> (match c2 with
            | Int (b) -> Bool (a==b)
            | _ -> raise (TypeError "Type error: Equal: Int"))
          | Bool (a) -> (match c2 with
            | Bool (b) -> Bool (a==b)
            | _ -> raise (TypeError "Type error: Equal: Bool"))
          | String (a) -> (match c2 with
            | String (b) -> Bool (a==b)
            | _ -> raise (TypeError "Type error: Equal: String"))
          | _ -> raise (TypeError "Type error: Equal"))
      | NotEqual -> let c1 = eval_expr env e1 in let c2 = eval_expr env e2 in
        (match c1 with
          | Int (a) -> (match c2 with
            | Int (b) -> Bool (a!=b)
            | _ -> raise (TypeError "Type error: NotEqual: Int"))
          | Bool (a) -> (match c2 with
            | Bool (b) -> Bool (a!=b)
            | _ -> raise (TypeError "Type error: NotEqual: Bool"))
          | String (a) -> (match c2 with
            | String (b) -> Bool (a!=b)
            | _ -> raise (TypeError "Type error: NotEqual: String"))
          | _ -> raise (TypeError "Type error: NotEqual"))
      | Or -> let c1 = eval_expr env e1 in let c2 = eval_expr env e2 in
        (match c1 with
          | Bool (a) -> (match c2 with
            | Bool (b) -> Bool (a||b)
            | _ -> raise (TypeError "Type error: Or: Bool"))
          | _ -> raise (TypeError "Type error: Or"))
      | And -> let c1 = eval_expr env e1 in let c2 = eval_expr env e2 in
        (match c1 with
          | Bool (a) -> (match c2 with
            | Bool (b) -> Bool (a&&b)
            | _ -> raise (TypeError "Type error: And: Bool"))
          | _ -> raise (TypeError "Type error: And")))
    | If (e1, e2, e3) -> let v1 = eval_expr env e1 in
      (match v1 with
        | Bool (x) -> (match x with
          | true -> (eval_expr env e2)
          | false -> (eval_expr env e3))
        | _ -> raise (TypeError "Type error: If: Bool"))
    | Let (x, y, e1, e2) -> (match y with
      | false -> let v1 = (eval_expr env e1) in (eval_expr (extend env x v1) e2)
      | true -> let tenv = extend_tmp env x in let v1 = (eval_expr tenv e1) in
        let _ = (update tenv x v1) in (eval_expr tenv e2))
      (*
      | true -> let v1 = eval_expr (extend_tmp env x) e1 in
        (eval_expr (extend env x v1) e2))
        *)
    | Fun (x, e1) -> (eval_expr env (Value (Closure (env, x, e1))))
    | FunctionCall (e1, e2) -> let a = eval_expr env e1 in (match a with
      | Closure (en, x, e) -> let v1 = eval_expr env e2 in (eval_expr (extend en x v1) e)
      | _ -> raise (TypeError "Type error: FunctionCall"))
    (*
    | FunctionCall (e1, e2) -> (match e2 with
      | FunctionCall (e3, e4) -> (eval_expr evn (FunctionCall (e3, e4)))
      | _ -> (match (lookup env e1) with
        | Closure (en, y, e) -> (match e with
          | Fun (z, e3) -> (eval_expr en (FunctionCall (z, e3)))
          | _ -> let v1 = (eval_expr en e) in (eval_expr (extend en y v1) y))
        | _ -> raise (TypeError "Type error: FunctionCall")))
        *)

(* Part 2: Evaluating mutop directive *)

(* Evaluates MicroCaml mutop directive [m] in environment [env],
   returning a possibly updated environment paired with
   a value option; throws an exception on error *)
let eval_mutop env m = match m with
  | Def (x, e) -> let tenv = extend_tmp env x in let v1 = (eval_expr tenv e) in
    let _ = (update tenv x v1) in (tenv, Some (eval_expr tenv e))
  | Expr (e) -> (env, Some (eval_expr env e))
  | NoOp -> ([], None)