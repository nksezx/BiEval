-- Traditional call-by-value interpreter.

import Debug.Trace

data Expr
  = EVar Int
  | ELam Expr
  | EApp Expr Expr
  | EInt Int
  | EBool Bool
  | EList [Int]
  | EPrim PrimOp Expr Expr
  | EFix Expr
  | EIf Expr Expr Expr
  | ELet Expr Expr Expr
  | ECons Expr Expr
  | EHead Expr
  | ETail Expr
  | EFoldl PrimOp Expr Expr
  | EFoldr PrimOp Expr Expr
  | EFreeze Expr
  | ETree Tree
  | EApplyLens Expr Expr
  | EUpdateApp Expr
  deriving (Show, Eq)

data Value
  = VInt Int
  | VBool Bool
  | VClosure Expr Env
  | VList [Int]
  | VTree Tree
  | VDiff [DiffOp]
  deriving (Show, Eq)

data Tree = EmptyTree | Node Int Tree Tree
  deriving (Show, Eq)

data PrimOp = Add | Sub | Mul | Lt | Gt | Eq | Le | Ge | Diff | Merge
  deriving (Show, Eq)

data Pattern = Value Value | Expr Expr 
  deriving (Show, Eq)

data DiffOp = Keep | Delete | Insert Value | Update Value
  deriving (Show, Eq)

type Env = [Pattern]

eval :: Env -> Expr -> Value
eval env term = case term of
  EVar n -> case (env !! n) of
    Value v -> v
    Expr (EFix e) -> eval [] (EFix e)

  ELam a -> VClosure a env
  
  EApp a (EFix b) ->
    let VClosure c env' = eval env a in
      eval ((Expr (EFix b)) : env') c

  EApp a b -> 
    let VClosure c env' = eval env a in
    let v = eval env b in
      eval ((Value v) : env') c

  EFix e -> eval env (EApp e (EFix e))

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

  ECons e1 e2 -> 
      let VInt v1 = eval env e1 in
      let VList v2 = eval env e2 in
        VList (v1:v2)
  EList xs -> VList xs
  EHead e  -> head' (eval env e)
  ETail e  -> tail' (eval env e)

  EFoldl op e1 e2 ->
    let VInt v1 = eval env e1 in
    let VList v2 = eval env e2 in
      eval env (EApp (EApp (EFix (
        ELam (
          ELam (
            ELam (
              EIf (EPrim Eq (EVar 0) (EList []))
              (EVar 1)
              (EApp (EApp (EVar 2) (EPrim op (EVar 1) (EHead (EVar 0)))) (ETail (EVar 0)))
            )
          )
        )
      )) (EInt v1)) (EList v2))

  EFoldr op e1 (EList []) -> eval env e1
  EFoldr op e1 e2         ->
    let VInt head = eval env (EHead e2) in
    let VList xs = eval env (ETail e2) in
    let VInt rest = eval env (EFoldr op e1 (EList xs)) in
      eval env (EPrim op (EInt head) (EInt rest))
    
  EFreeze e -> eval env e

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
    let (((Value v1'):env2), e2') = evalUpdate ((Value (eval env e1)):env) e2 newValue in
    let (env1, e1') = evalUpdate env e1 v1' in
    let env' = merge env1 env2 env in
      trace ("\nenv1: " ++ show env1 ++ "\nenv2: " ++ show env2)
      (env', ELet var e1' e2')

  -- U-APP
  (EApp e1 e2, _) ->
    let VClosure ef envf = eval env e1 in
    let v2 = case e2 of
              EFix e    -> Expr (EFix e)
              otherwise -> Value (eval env e2) in
    let (env', ef') = evalUpdate (v2:envf) ef newValue in
    let (env1, e1') = evalUpdate env e1 (VClosure ef' (tail env')) in
      case (head env') of
        Value v2' -> let (env2, e2') = evalUpdate env e2 v2' in (merge env1 env2 env, EApp e1' e2')
        Expr e'   -> ([], EFix e1')

  -- U-FIX
  --   (EFix e, _) -> evalUpdate env (EApp e (EFix e)) newValue
  (EFix e, _) ->
    -- let (env', EApp e1 e2) = evalUpdate env (EApp e (EFix e)) newValue in
      let (env', expr) = evalUpdate env (EApp e (EFix e)) newValue in
      -- trace ("expr" ++ show expr) 
        (case expr of
          EApp _ (EFix e') -> (env', EFix e')
          otherwise -> (env', expr))

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

  -- U-FREEZE
  (EFreeze e, _) -> (env, EFreeze e)

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

  -- U-Foldr // not defined for other primitive operations
  (EFoldr Add e1 (EList []), _) -> 
    let (env', e1') = evalUpdate env e1 newValue in
      (env', EFoldr Add e1' (EList []))
  (EFoldr Add e1 e2, _) ->
    let VInt head = eval env (EHead e2) in
    let VList xs = eval env (ETail e2) in
    let (env', EPrim Add (EInt head') (EFoldr Add e1' (EList xs'))) = evalUpdate env (EPrim Add (EInt head) (EFoldr Add e1 (EList xs))) newValue in
      (env', EFoldr Add e1' (EList (head':xs')))

  -- U-CONS
  (ECons e1 e2, VList (v1':v2')) ->
    let (env1, e1') = evalUpdate env e1 (VInt v1') in
    let (env2, e2') = evalUpdate env e2 (VList v2') in
      (merge env1 env2 env, ECons e1' e2')

  (EList [], VList v) ->
    trace (show v) (env, EList v)

  (EList _, VList v) ->
    (env, EList v)

  (EHead e, VInt v) ->
    let VList l = eval env e in
    let newList = v:(tail l) in
      evalUpdate env e (VList newList)

  (ETail e, VList v) ->
    let VList l = eval env e in
    let newList = (head l):v in
      evalUpdate env e (VList newList)

  -- TODO: U-LIST
  -- (e, VDiff ((Insert (VInt v')):delta)) -> let (env', EList xs') = evalUpdate env e (VDiff delta) in (env', EList (v':xs'))
  -- (EList [], VDiff [])        -> (env, EList [])
  -- (EList (x:xs), VDiff _)      -> case newValue of
  --   VDiff (Keep:delta)        -> let (env', EList xs') = evalUpdate env (EList xs) (VDiff delta) in (env', EList (x:xs'))
  --   VDiff (Delete:delta)      -> let (env', EList xs') = evalUpdate env (EList xs) (VDiff delta) in (env', EList xs')
  --   VDiff ((Update v'):delta) -> let (env1, (EInt x')) = evalUpdate env (EInt x) v' in
  --                                let (env2, (EList xs')) = evalUpdate env (EList xs) (VDiff delta) in
  --                                let env' = merge env1 env2 env in
  --                                   (env', EList (x':xs'))
  -- (EList e, VList _) -> let v = eval env (EList e) in
  --                       let delta = snd $ diff v newValue in evalUpdate env (EList e) (VDiff delta)
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
eq (VList a) (VList b) = VBool (a == b)

head' :: Value -> Value
head' (VList [])     = VList []
head' (VList (x:xs)) = VInt x

tail' :: Value -> Value
tail' (VList [])     = VList []
tail' (VList (x:xs)) = VList xs

emptyEnv :: Env
emptyEnv = []

emptyList :: Value
emptyList = VList []

-- merge(E1, E2, E)
merge :: Env -> Env -> Env -> Env
merge [] [] [] = []
merge (v1:vs1) (v2:vs2) (v:vs) = if (v2 /= v) then (v2:(merge vs1 vs2 vs)) else (v1:(merge vs1 vs2 vs))

-- updateList(n,list,new)
updateList :: Int -> [Pattern] -> Value -> [Pattern]
updateList 0 list new = ((Value new) : (tail list))
updateList n list new = (head(list) : (updateList (n-1) (tail list) new))

addToTail :: Value -> [Value] -> [Value]
addToTail a [] = [a]
addToTail a (x:xs) = x : (addToTail a xs)

diff :: Value -> Value -> (Int, [DiffOp])
diff (VList v) (VList v') = case v of
  []     -> (length v', turnTo v')
  (x:xs) -> if (v' == [])
    then (length v, replicate (length v) Delete)
    else let x':xs' = v' in
            if (x == x') 
              then let (n, opList) = diff (VList xs) (VList xs') in (n, Keep:opList)
              else compareBefore x' (diff (VList xs) (VList xs')) (diff (VList (x:xs)) (VList xs')) (diff (VList xs) (VList (x':xs')))

turnTo :: [Int] -> [DiffOp]
turnTo v = case v of
  []        -> []
  (x:xs)    -> (Insert (VInt x)) : turnTo xs

compareBefore :: Int -> (Int, [DiffOp]) -> (Int, [DiffOp]) -> (Int, [DiffOp]) -> (Int, [DiffOp])
compareBefore v' (n1, list1) (n2, list2) (n3, list3) =
  if (n1 == foldr min maxBound [n1, n2, n3])
    then (n1+1, (Update (VInt v')):list1)
    else if (n2 == min n2 n3)
            then (n2+1, (Insert (VInt v')):list2)
            else (n3+1, Delete:list3)

-- -- test for eval
-- -- (\x y -> x + y) 10 20
-- test1 :: Value
-- test1 = eval emptyEnv $ EApp (EApp (ELam (ELam (EPrim Add (EVar 0) (EVar 1)))) (EInt 10)) (EInt 20)

-- -- If (2 < 3) 10 20
-- test2 :: Value
-- test2 = eval emptyEnv $ EIf (EPrim Lt (EInt 2) (EInt 3)) (EInt 10) (EInt 20)

-- -- factorial
-- fac :: Expr
-- fac = EFix (
--         ELam (
--             ELam (
--                 EIf (EPrim Eq (EVar 0) (EInt 1)) 
--                 (EInt 1) 
--                 (EPrim Mul (EVar 0) (EApp (EVar 1) (EFreeze (EPrim Sub (EVar 0) (EInt 1)))))
--             )
--         )
--     )

-- test3 :: Value
-- test3 = eval emptyEnv $ EApp fac (EInt 5)

-- test3' :: (Env, Expr)
-- test3' = (evalUpdate emptyEnv $ EApp fac (EInt 4)) (VInt 48)

-- -- let x = 1 let y = 2 in x+y
-- test4 :: Value
-- test4 = eval emptyEnv $ (ELet (EVar 0) (EInt 2) (ELet (EVar 1) (EInt 3) (EPrim Add (EVar 0) (EVar 1))))

-- -- head (1 :: [2,3,4])
-- test5 :: Value
-- test5 = eval emptyEnv $ (EHead (ECons (EInt 1) (EList [2,3,4])))

-- -- foldl (+) 0 [1,2,3,4]
-- test6 :: Value
-- test6 = eval emptyEnv $ (EFoldl Add (EInt 0) (EList [1,2,3,4]))

-- --test6' :: Value
-- test6' = eval emptyEnv $ (EFoldr Add (EInt 0) (EList [1,2,3,4]))

-- -- test for update
-- -- let x = 1 in x "1 -> 2"
-- test7 :: (Env, Expr)
-- test7 = (evalUpdate emptyEnv $ (ELet (EVar 0) (EInt 1) (EVar 0))) (VInt 3)

-- -- if True 10 20 "10 -> 30"
-- test8 :: (Env, Expr)
-- test8 = (evalUpdate emptyEnv $ (EIf (EBool True) (EInt 10) (EInt 20))) (VInt 30)

-- -- if True (freeze 10) 20 "10 -> 30"
-- test9 :: (Env, Expr)
-- test9 = (evalUpdate emptyEnv $ (EIf (EBool True) (EFreeze (EInt 10)) (EInt 20))) (VInt 30)

-- -- (\x -> x)10 "10 -> 20"
-- test10 :: (Env, Expr)
-- test10 = (evalUpdate emptyEnv $ (EApp (ELam (EVar 0)) (EInt 10))) (VInt 20)

-- -- let x = 1 let y = 2 in x+y "3 -> 5"
-- test11 :: (Env, Expr)
-- test11 = (evalUpdate emptyEnv $ (ELet (EVar 0) (EInt 1) (ELet (EVar 1) (EInt 2) (EPrim Add (EVar 0) (EVar 1))))) (VInt 5)

-- -- (\x y -> x + y) 10 20 "30 -> 50"
-- test12 :: (Env, Expr)
-- test12 = (evalUpdate emptyEnv $ EApp (EApp (ELam (ELam (EPrim Add (EVar 0) (EVar 1)))) (EInt 10)) (EInt 20)) (VInt 50)

-- -- (\x y -> x + y + 1) 10 20 "31 -> 51"
-- test13 :: (Env, Expr)
-- test13 = (evalUpdate emptyEnv $ EApp (EApp (ELam (ELam (EPrim Add (EPrim Add (EVar 0) (EVar 1)) (EInt 1)))) (EInt 10)) (EInt 20)) (VInt 51)

-- -- 2 < 3 "True -> False"
-- test14 :: (Env, Expr)
-- test14 = (evalUpdate emptyEnv $ EPrim Lt (EInt 2) (EInt 3)) (VBool False)

-- -- (\x -> x + (\y -> y + 1) x) 10 "21 -> 31"
-- test15 :: (Env, Expr)
-- test15 = (evalUpdate emptyEnv $ EApp (ELam (EPrim Add (EVar 0) (EApp (ELam (EPrim Add (EVar 1) (EInt 1))) (EVar 0)))) (EInt 10)) (VInt 31)

-- -- foldr (+) 0 [1,2,3] "6->5"
-- test16 :: (Env, Expr)
-- test16 = (evalUpdate emptyEnv $ EFoldr Add (EInt 0) (EList [1,2,3])) (VInt 5)

-- -- 2+3 “5->6”
-- test17 :: (Env, Expr)
-- test17 = (evalUpdate emptyEnv $ EPrim Add (EFreeze (EInt 2)) (EInt 3)) (VInt 6)

-- -- [1,2,3] "[1,2,3] -> [0,1,2,0,3,4]"
-- test18 :: (Env, Expr)
-- test18 = (evalUpdate emptyEnv $ EList [1,2,3]) (VList [0,1,2,0,3,4])

map_ :: Expr
map_ = EFix (
        ELam (
          ELam (
            ELam (
              EIf (EPrim Eq (EVar 0) (EList []))
              (EList [])
              (ECons (EApp (EVar 1) (EHead (EVar 0))) (EApp (EApp (EVar 2) (EVar 1)) (ETail (EVar 0))))
            )
          )
        )
      )

-- map (+1) [0,1,2]
test19 :: Value
test19 = eval emptyEnv $ EApp (EApp map_ (ELam (EPrim Add (EInt 1) (EVar 0)))) (EList [0,1,2])

test19' :: (Env, Expr)
test19' = (evalUpdate emptyEnv $ EApp (EApp map_ (ELam (EPrim Add (EInt 1) (EVar 0)))) (EList [1,2,3])) (VList [5,4,4])

-- fib
-- test20 :: Value
-- test20 = eval emptyEnv $ EApp (EFix (ELam (ELam (EIf (EPrim Le (EVar 0) (EInt 1)) (EInt 1) (EPrim Add (EApp (EVar 1) (EPrim Sub (EVar 0) (EInt 1))) (EApp (EVar 1) (EPrim Sub (EVar 0) (EInt 2)))))))) (EInt 7)

-- test20' :: (Env, Expr)
-- test20' = (evalUpdate emptyEnv $ EApp (EFix (ELam (ELam (EIf (EPrim Le (EVar 0) (EInt 1)) (EInt 1) (EPrim Add (EApp (EVar 1) (EPrim Sub (EVar 0) (EInt 1))) (EApp (EVar 1) (EPrim Sub (EVar 0) (EInt 2)))))))) (EInt 3)) (VInt 6)

-- -- test recursion
-- test21 :: Value
-- test21 = eval emptyEnv $ EApp (EFix (ELam (ELam (EIf (EPrim Eq (EVar 0) (EInt 1)) (EInt 1) (EPrim Mul (EVar 0) (EApp (EVar 1) (EFreeze (EPrim Sub (EVar 0) (EInt 1))))))))) (EInt 8)

-- range 1 3 = [1,2,3]
-- range :: Expr
-- range = EFix (
--         ELam (
--             ELam (
--                 ELam (
--                   EIf (EPrim Ge (EVar 1) (EPrim Add (EVar 0) (EInt 1))) 
--                   (EList []) 
--                   (ECons (EVar 1) (EApp (EApp (EVar 2) (EPrim Add (EVar 1) (EInt 1))) (EVar 0)))
--                 )
--             )
--         )
--     )

-- test22 :: Value
-- test22 = eval emptyEnv $ EApp (EApp range (EInt 0)) (EInt 5)

-- test22' :: (Env, Expr)
-- test22' = (evalUpdate emptyEnv $ EApp (EApp range (EInt 2)) (EInt 3)) (VList [2,3,4])

-- max i j
-- max_ :: Expr
-- max_ = ELam (
--         ELam (
--           EIf (EPrim Ge (EVar 1) (EVar 0))
--           (EVar 1)
--           (EVar 0)
--         )
--       )

-- test23 :: Value
-- test23 = eval emptyEnv $ EApp (EApp max_ (EInt 2)) (EInt 3)

-- test23' :: (Env, Expr)
-- test23' = (evalUpdate emptyEnv $ EApp (EApp max_ (EInt 2)) (EInt 3)) (VInt 1)

-- reverse_ :: Expr
-- reverse_ = EFix (
--             ELam (
--               ELam (
--                 ELam (
--                   EIf (EPrim (Eq) (EVar 0) (EList []))
--                   (EVar 1)
--                   (EApp (EApp (EVar 2) (ECons (EHead (EVar 0)) (EVar 1))) (ETail (EVar 0)))
--                 )
--               )
--             )
--           )
-- test24 :: Value
-- test24 = eval emptyEnv $ EApp (EApp reverse_ (EList [])) (EList [1,2,3])

-- test24' :: (Env, Expr)
-- test24' = (evalUpdate emptyEnv $ EApp (EApp reverse_ (EList [])) (EList [1,2,3])) (VList [4,3,2,1])

test23 :: Value 
test23 = eval emptyEnv $ ELet (EVar 0) (EInt 1) (ELet (EVar 1) (EPrim Mul (EInt 2) (EVar 0)) (EPrim Add (EVar 1) (EVar 0)))

test23' :: (Env, Expr)
test23' = (evalUpdate emptyEnv $ ELet (EVar 0) (EInt 1) (ELet (EVar 1) (EPrim Mul (EInt 2) (EVar 0)) (EPrim Add (EVar 1) (EVar 0)))) (VInt 6)

test25 :: Value
test25 = eval [Value (VInt 1)] $ EApp (ELam (EPrim Add (EVar 1) (EVar 0))) (EPrim Mul (EInt 2) (EVar 0))

test25' :: (Env, Expr)
test25' = (evalUpdate [Value (VInt 1)] $ EApp (ELam (EPrim Add (EVar 1) (EVar 0))) (EPrim Mul (EInt 2) (EVar 0))) (VInt 5)