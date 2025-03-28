{-# LANGUAGE FlexibleInstances, OverloadedStrings, BangPatterns #-}
{-# LANGUAGE InstanceSigs #-}

module Language.Nano.TypeCheck where

import Language.Nano.Types
import Language.Nano.Parser

import qualified Data.List as L
import           Text.Printf (printf)  
import           Control.Exception (throw)

--------------------------------------------------------------------------------
typeOfFile :: FilePath -> IO Type
typeOfFile f = parseFile f >>= typeOfExpr

typeOfString :: String -> IO Type
typeOfString s = typeOfExpr (parseString s)

typeOfExpr :: Expr -> IO Type
typeOfExpr e = do
  let (!st, t) = infer initInferState preludeTypes e
  if (length (stSub st)) < 0 then throw (Error ("count Negative: " ++ show (stCnt st)))
  else return t

--------------------------------------------------------------------------------
-- Problem 1: Warm-up
--------------------------------------------------------------------------------

-- | Things that have free type variables
class HasTVars a where
  freeTVars :: a -> [TId]

-- | Type variables of a type
instance HasTVars Type where
  freeTVars :: Type -> [TId]
  freeTVars TInt            = []
  freeTVars TBool           = []
  freeTVars (TVar a)        = [a]
  freeTVars (t1 :=> t2)     = L.union (freeTVars t1) (freeTVars t2)
  freeTVars (TList t)       = freeTVars t

-- | Free type variables of a poly-type (remove forall-bound vars)
instance HasTVars Poly where
  freeTVars :: Poly -> [TId]
  freeTVars (Mono t)        = freeTVars t
  freeTVars (Forall a p)    = L.delete a (freeTVars p)

-- | Free type variables of a type environment
instance HasTVars TypeEnv where
  freeTVars :: TypeEnv -> [TId]
  freeTVars gamma   = concat [freeTVars s | (x, s) <- gamma]  
  
-- | Look up a variable in a type environment
lookupVarType :: Id -> TypeEnv -> Poly
lookupVarType x ((y, s) : gamma)
  | x == y    = s
  | otherwise = lookupVarType x gamma
lookupVarType x [] = throw (Error ("unbound variable: " ++ x))

-- | Extend a type environment with a new binding
extendTypeEnv :: Id -> Poly -> TypeEnv -> TypeEnv
extendTypeEnv x s gamma = (x,s) : gamma  

-- | Look up a type variable in a substitution;
--   if not present, return the variable unchanged
lookupTVar :: TId -> Subst -> Type
lookupTVar a [] = TVar a
lookupTVar a ((b,t):sub)
  | a == b    = t
  | otherwise = lookupTVar a sub

-- | Remove a type variable from a substitution
removeTVar :: TId -> Subst -> Subst
removeTVar a [] = []
removeTVar a ((b,t):sub)
  | a == b    = removeTVar a sub
  | otherwise = (b,t) : removeTVar a sub
     
-- | Things to which type substitutions can be applied
class Substitutable a where
  apply :: Subst -> a -> a
  
-- | Apply substitution to type
instance Substitutable Type where
  apply :: Subst -> Type -> Type
  apply _ TInt = TInt
  apply _ TBool = TBool
  apply sub t@(TVar a) =
    let t' = lookupTVar a sub
    in if t' == TVar a then t else apply sub t'
  apply sub (t1 :=> t2) = apply sub t1 :=> apply sub t2
  apply sub (TList t)   = TList (apply sub t)

-- | Apply substitution to poly-type
instance Substitutable Poly where    
  apply :: Subst -> Poly -> Poly
  apply sub (Mono t)       = Mono (apply sub t)
  apply sub (Forall a p)   = Forall a (apply (removeTVar a sub) p)

-- | Apply substitution to (all poly-types in) another substitution
instance Substitutable Subst where  
  apply :: Subst -> Subst -> Subst
  apply sub to = zip keys (map (apply sub) vals)
    where
      (keys, vals) = unzip to
      
-- | Apply substitution to a type environment
instance Substitutable TypeEnv where  
  apply :: Subst -> TypeEnv -> TypeEnv
  apply sub gamma = zip keys (map (apply sub) vals)
    where
      (keys, vals) = unzip gamma
      
-- | Extend substitution with a new type assignment
extendSubst :: Subst -> TId -> Type -> Subst
extendSubst sub a t =
  let t'   = apply sub t
      sub' = apply [(a, t')] (removeTVar a sub)
  in (a, t') : sub'
      
--------------------------------------------------------------------------------
-- Problem 2: Unification
--------------------------------------------------------------------------------
      
-- | State of the type inference algorithm      
data InferState = InferState { 
    stSub :: Subst -- ^ current substitution
  , stCnt :: Int   -- ^ number of fresh type variables generated so far
} deriving (Eq,Show)

-- | Initial state: empty substitution; 0 type variables
initInferState = InferState [] 0

-- | Fresh type variable number n
freshTV n = TVar ("a" ++ show n)
    
-- | Extend the current substitution of a state with a new type assignment   
extendState :: InferState -> TId -> Type -> InferState
extendState (InferState sub n) a t = InferState (extendSubst sub a t) n
        
-- | Unify a type variable with a type; 
--   if successful return an updated state, otherwise throw an error
unifyTVar :: InferState -> TId -> Type -> InferState
unifyTVar st a t
  | t == TVar a = st
  | a `elem` freeTVars t = throw (Error ("type error: cannot unify " ++ a ++ " and " ++ show t ++ " (occurs check)"))
  | otherwise = extendState st a t
    
-- | Unify two types;
--   if successful return an updated state, otherwise throw an error
unify :: InferState -> Type -> Type -> InferState
unify st t1 t2 =
  let t1' = apply (stSub st) t1
      t2' = apply (stSub st) t2
  in case (t1', t2') of
      (TInt, TInt)         -> st
      (TBool, TBool)       -> st
      (TVar a, _)          -> unifyTVar st a t2'
      (_, TVar a)          -> unifyTVar st a t1'
      (t1a :=> t1r, t2a :=> t2r) ->
          let st'  = unify st t1a t2a
              st'' = unify st' (apply (stSub st') t1r) (apply (stSub st') t2r)
          in st''
      (TList t1a, TList t2a) -> unify st t1a t2a
      _ -> throw (Error ("type error: cannot unify " ++ show t1' ++ " and " ++ show t2'))

--------------------------------------------------------------------------------
-- Problem 3: Type Inference
--------------------------------------------------------------------------------    
  
infer :: InferState -> TypeEnv -> Expr -> (InferState, Type)
infer st _   (EInt _) = (st, TInt)
infer st _   (EBool _) = (st, TBool)
infer st gamma (EVar x) =
  let poly = lookupVarType x gamma
      (n, t) = instantiate (stCnt st) poly
  in (st { stCnt = n }, t)
infer st gamma (ELam x body) =
  let a    = freshTV (stCnt st)
      st'  = st { stCnt = stCnt st + 1 }
      gamma' = extendTypeEnv x (Mono a) gamma
      (st'', tBody) = infer st' gamma' body
  in (st'', a :=> tBody)
infer st gamma (EApp e1 e2) =
  let (st1, t1) = infer st gamma e1
      gamma'    = apply (stSub st1) gamma
      (st2, t2) = infer st1 gamma' e2
      a         = freshTV (stCnt st2)
      st3       = st2 { stCnt = stCnt st2 + 1 }
      st4       = unify st3 t1 (t2 :=> a)
  in (st4, apply (stSub st4) a)
infer st gamma (ELet x e1 e2) =
  let a    = freshTV (stCnt st)
      st'  = st { stCnt = stCnt st + 1 }
      gamma' = extendTypeEnv x (Mono a) gamma
      (st1, t1) = infer st' gamma' e1
      st1' = unify st1 a t1
      t1'  = apply (stSub st1') t1
      poly = generalize (apply (stSub st1') gamma) t1'
      gamma'' = extendTypeEnv x poly gamma
      (st2, t2) = infer st1' gamma'' e2
  in (st2, t2)
infer st gamma (EBin op e1 e2) = infer st gamma asApp
  where
    asApp = EApp (EApp (EVar (show op)) e1) e2
infer st gamma (EIf c e1 e2) = infer st gamma asApp
  where
    asApp = EApp (EApp (EApp (EVar "if") c) e1) e2
infer st gamma ENil = infer st gamma (EVar "[]")

-- | Generalize type variables inside a type
generalize :: TypeEnv -> Type -> Poly
generalize gamma t =
  let ft   = freeTVars t
      fenv = freeTVars gamma
      genVars = filter (`notElem` fenv) ft
  in foldr Forall (Mono t) genVars
    
-- | Instantiate a polymorphic type into a mono-type with fresh type variables
instantiate :: Int -> Poly -> (Int, Type)
instantiate n s = helper n [] s
  where
    helper :: Int -> Subst -> Poly -> (Int, Type)
    helper n sub (Mono t)     = (n, apply sub t)
    helper n sub (Forall a s) = helper (n + 1) ((a, freshTV n):sub) s
      
-- | Types of built-in operators and functions      
preludeTypes :: TypeEnv
preludeTypes =
  [ ("+",    Mono (TInt :=> TInt :=> TInt))
  , ("-",    Mono (TInt :=> TInt :=> TInt))
  , ("*",    Mono (TInt :=> TInt :=> TInt))
  , ("/",    Mono (TInt :=> TInt :=> TInt))
  , ("==",   forall "a" (TVar "a" :=> TVar "a" :=> TBool))
  , ("!=",   forall "a" (TVar "a" :=> TVar "a" :=> TBool))
  , ("<",    Mono (TInt :=> TInt :=> TBool))
  , ("<=",   Mono (TInt :=> TInt :=> TBool))
  , ("&&",   Mono (TBool :=> TBool :=> TBool))
  , ("||",   Mono (TBool :=> TBool :=> TBool))
  , ("if",   forall "a" (TBool :=> (TVar "a" :=> (TVar "a" :=> TVar "a"))))
  -- lists:
  , ("[]",   forall "a" (TList (TVar "a")))
  , (":",    forall "a" (TVar "a" :=> TList (TVar "a") :=> TList (TVar "a")))
  , ("head", forall "a" (TList (TVar "a") :=> TVar "a"))
  , ("tail", forall "a" (TList (TVar "a") :=> TList (TVar "a")))
  ]
