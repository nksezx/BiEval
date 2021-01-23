-- Traditional call-by-value interpreter.

import Debug.Trace

data Expr
  = EVar Int
  | ELam Expr
  | EApp Expr Expr
  | EInt Int
  | EBool Bool
  | EPrim PrimOp Expr Expr
  | EIf Expr Expr Expr
  | ELet Expr Expr Expr
  deriving (Show, Eq)

data Value
  = VInt Int
  | VBool Bool
  | VClosure Expr Env
  deriving (Show, Eq)

data PrimOp = Add | Sub | Mul | Lt | Gt | Eq | Le | Ge
  deriving (Show, Eq)

type Env = [Value]

eval :: Env -> Expr -> Value
eval env term = case term of
  EVar n -> env !! n

  ELam a -> VClosure a env

  EApp a b -> 
    let VClosure c env' = eval env a in
    let v = eval env b in
      eval (v : env') c

  EInt n -> VInt n
  EBool b -> VBool b

  EPrim Add a b -> add (eval env a) (eval env b)
  EPrim Sub a b -> sub (eval env a) (eval env b)
  EPrim Mul a b -> mul (eval env a) (eval env b)
  EPrim Lt  a b -> lt  (eval env a) (eval env b)
  EPrim Gt  a b -> gt  (eval env a) (eval env b)
  EPrim Eq  a b -> eq  (eval env a) (eval env b)
  EPrim Le  a b -> le  (eval env a) (eval env b)
  EPrim Ge  a b -> ge  (eval env a) (eval env b)

  EIf (EBool True) e2 _  -> eval env e2
  EIf (EBool False) _ e3 -> eval env e3
  EIf e1 e2 e3 -> 
    let VBool v = eval env e1 in
      eval env (EIf (EBool v) e2 e3)

  ELet _ e1 e2 -> eval env (EApp (ELam e2) e1)


evalUpdate :: Env -> Expr -> Value -> (Env, Expr)
evalUpdate env term newValue = 
  trace ("term   " ++ show term ++ "\nenv   " ++ show env ++ "\nnewValue   " ++ show newValue++"\n")
  (case (term, newValue) of
  -- U-CONST
  (EInt n, _)  -> let VInt v' = newValue in (env, EInt v')
  (EBool b, _) -> let VBool v' = newValue in (env, EBool v')

  -- U-FUN
  (ELam e, _)  -> let VClosure e' env' = newValue in (env', ELam e')
    
  -- U-VAR
  (EVar n, _)  -> (updateList n env newValue, EVar n)

  -- U-LET
  (ELet var e1 e2, _) -> 
    let ((v1':env2), e2') = evalUpdate ((eval env e1):env) e2 newValue in
    let (env1, e1') = evalUpdate env e1 v1' in
    let env' = merge env1 env2 env in
      trace ("\nenv1: " ++ show env1 ++ "\nenv2: " ++ show env2)
      (env', ELet var e1' e2')

  -- U-APP
  (EApp e1 e2, _) ->
    let VClosure ef envf = eval env e1 in
    let v2 = eval env e2 in
    let (env', ef') = evalUpdate (v2:envf) ef newValue in
    let (env1, e1') = evalUpdate env e1 (VClosure ef' (tail env')) in
    let (env2, e2') = evalUpdate env e2 (head env') in 
      (merge env1 env2 env, EApp e1' e2')

  -- U-IF-TRUE
  (EIf (EBool True) e2 e3, _) ->
    let (env2, e2') = evalUpdate env e2 newValue in
      (merge env env2 env, EIf (EBool True) e2' e3)

  -- U-IF-FALSE
  (EIf (EBool False) e2 e3, _) ->
    let (env3, e3') = evalUpdate env e3 newValue in
      (merge env env3 env, EIf (EBool False) e2 e3')

  -- U-IF
  (EIf e1 e2 e3, _) ->
    let VBool v = eval env e1 in
      let (env', EIf _ e2' e3') = evalUpdate env (EIf (EBool v) e2 e3) newValue in
        (env', EIf e1 e2' e3')

  -- U-PLUS-1 
  (EPrim Add e1 e2, _) -> 
    let VInt n' = newValue in
      let VInt n1 = eval env e1 in
        let (env2, e2') = evalUpdate env e2  (VInt (n' - n1)) in
          (env2, (EPrim Add e1 e2'))

  -- -- U-PLUS-2
  -- (EPrim Add e1 e2, _) -> 
  --   let VInt n' = newValue in
  --   let VInt n2 = eval env e2 in
  --   let (env1, e1') = evalUpdate env e1  (VInt (n' - n2)) in
  --     (env1, (EPrim Add e1' e2))

  -- U-MUL-1 
  (EPrim Mul e1 e2, _) -> 
    let VInt n' = newValue in
      let VInt n1 = eval env e1 in
        let (env2, e2') = evalUpdate env e2  (VInt (n' `div` n1)) in
          (env2, (EPrim Mul e1 e2'))

  -- -- U-MUL-2
  -- (EPrim Mul e1 e2, _) -> 
  --   let VInt n' = newValue in
  --   let VInt n2 = eval env e2 in
  --   let (env1, e1') = evalUpdate env e1  (VInt (n' `div` n2)) in
  --     (env1, (EPrim Mul e1' e2))

  -- U-SUB-1
  (EPrim Sub e1 e2, _) -> 
    let VInt n' = newValue in
      let VInt n1 = eval env e1 in
        let (env2, e2') = evalUpdate env e2  (VInt (n1 - n')) in
          (env2, (EPrim Sub e1 e2'))

  -- -- U-SUB-2
  -- (EPrim Sub e1 e2, _) ->
  --   let VInt n' = newValue in
  --   let VInt n2 = eval env e2 in
  --   let (env1, e1') = evalUpdate env e1  (VInt (n2 - n')) in
  --     (env1, (EPrim Sub e1' e2))

  -- U-LT
  (EPrim Lt e1 e2, _) ->
    let VBool b' = newValue in
    let VBool b = eval env (EPrim Lt e1 e2) in
      if (b' == not b)
        then (env, EPrim Ge e1 e2)
        else (env, EPrim Lt e1 e2)
  )

add :: Value -> Value -> Value
add (VInt a) (VInt b) = VInt (a + b)

sub :: Value -> Value -> Value
sub (VInt a) (VInt b) = VInt (a - b)

mul :: Value -> Value -> Value
mul (VInt a) (VInt b) = VInt (a * b)

lt :: Value -> Value -> Value
lt (VInt a) (VInt b) = VBool (a < b)

gt :: Value -> Value -> Value
gt (VInt a) (VInt b) = VBool (a > b)

le :: Value -> Value -> Value
le (VInt a) (VInt b) = VBool (a <= b)

ge :: Value -> Value -> Value
ge (VInt a) (VInt b) = VBool (a >= b)

eq :: Value -> Value -> Value
eq (VInt a) (VInt b)   = VBool (a == b)

emptyEnv :: Env
emptyEnv = []

-- merge(E1, E2, E)
merge :: Env -> Env -> Env -> Env
merge [] [] [] = []
merge (v1:vs1) (v2:vs2) (v:vs) = if (v2 /= v) then (v2:(merge vs1 vs2 vs)) else (v1:(merge vs1 vs2 vs))

-- updateList(n,list,new)
updateList :: Int -> [Value] -> Value -> [Value]
updateList 0 list new = new : (tail list)
updateList n list new = (head(list) : (updateList (n-1) (tail list) new))