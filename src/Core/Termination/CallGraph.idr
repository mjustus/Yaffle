module Core.Termination.CallGraph

import Core.Context
import Core.Context.Log
import Core.Env
import Core.TT
import Core.Evaluate

import Data.SnocList

%default covering

-- Drop any non-inf top level laziness annotations
dropLazy : Value f vars -> Core (Glued vars)
dropLazy val@(VDelayed _ r t)
    = case r of
           LInf => pure (asGlued val)
           _ => pure t
dropLazy val@(VDelay _ r t v)
    = case r of
           LInf => pure (asGlued val)
           _ => pure v
dropLazy val@(VForce fc r v sp)
    = case r of
           LInf => pure (asGlued val)
           _ => applyAll fc v (cast (map snd sp))
dropLazy val = pure (asGlued val)

-- Equal for the purposes of size change means, ignoring as patterns, all
-- non-metavariable positions are equal
scEq : Value f vars -> Value f' vars -> Core Bool

scEqSpine : Spine vars -> Spine vars -> Core Bool
scEqSpine [<] [<] = pure True
scEqSpine (sp :< (_, _, x)) (sp' :< (_, _, y))
    = do x' <- x
         y' <- y
         if !(scEq x' y')
            then scEqSpine sp sp'
            else pure False
scEqSpine _ _ = pure False

scEq' : Value f vars -> Value f' vars -> Core Bool
scEq' (VApp _ Bound n sp _) (VApp _ Bound n' sp' _)
    = if n == n'
         then scEqSpine sp sp'
         else pure False
-- Should never see this!
scEq' (VLocal _ idx _ sp) (VLocal _ idx' _ sp')
    = if idx == idx'
         then scEqSpine sp sp'
         else pure False
scEq' (VDCon _ _ t a sp) (VDCon _ _ t' a' sp')
    = if t == t'
         then scEqSpine sp sp'
         else pure False
scEq' (VTCon _ n a sp) (VTCon _ n' a' sp')
    = if n == n'
         then scEqSpine sp sp'
         else pure False
scEq' (VMeta{}) _ = pure True
scEq' _ (VMeta{}) = pure True
scEq' (VAs _ _ a p) p' = scEq p p'
scEq' p (VAs _ _ a p') = scEq p p'
scEq' (VDelayed _ _ t) (VDelayed _ _ t') = scEq t t'
scEq' (VDelay _ _ t x) (VDelay _ _ t' x')
     = if !(scEq t t') then scEq x x'
          else pure False
scEq' (VForce _ _ t [<]) (VForce _ _ t' [<]) = scEq t t'
scEq' (VPrimVal _ c) (VPrimVal _ c') = pure $ c == c'
scEq' (VErased _ _) (VErased _ _) = pure True
scEq' (VUnmatched _ _) (VUnmatched _ _) = pure True
scEq' (VType _ _) (VType _ _) = pure True
scEq' _ _ = pure False -- other cases not checkable

scEq x y = scEq' !(dropLazy x) !(dropLazy y)

data Guardedness = Toplevel | Unguarded | Guarded | InDelay

Show Guardedness where
  show Toplevel = "Toplevel"
  show Unguarded = "Unguarded"
  show Guarded = "Guarded"
  show InDelay = "InDelay"

assertedSmaller : Maybe (Glued [<]) -> Glued [<] -> Core Bool
assertedSmaller (Just b) a = scEq b a
assertedSmaller _ _ = pure False

-- Return whether first argument is structurally smaller than the second.
smaller : Bool -> -- Have we gone under a constructor yet?
          Maybe (Glued [<]) -> -- Asserted bigger thing
          Glued [<] -> -- Term we're checking
          Glued [<] -> -- Argument it might be smaller than
          Core Bool

smallerArg : Bool ->
             Maybe (Glued [<]) -> Glued [<] -> Glued [<] -> Core Bool
smallerArg inc big (VAs _ _ _ s) tm = smallerArg inc big s tm
smallerArg inc big s tm
      -- If we hit a pattern that is equal to a thing we've asserted_smaller,
      -- the argument must be smaller
    = if !(assertedSmaller big tm)
         then pure True
         else case tm of
                   VDCon _ _ _ _ sp
                       => anyM (smaller True big s)
                                (cast !(traverseSnocList (snd . snd) sp))
                   _ => case s of
                             VApp fc nt n sp@(_ :< _) _ =>
                                -- Higher order recursive argument
                                  smaller inc big
                                      (VApp fc nt n [<] (pure Nothing))
                                      tm
                             _ => pure False

smaller inc big _ (VErased _ _) = pure False -- Never smaller than an erased thing!
-- for an as pattern, it's smaller if it's smaller than the pattern
-- or if we've gone under a constructor and it's smaller than the variable
smaller True big s (VAs _ _ a t)
    = if !(smaller True big s a)
         then pure True
         else smaller True big s t
smaller True big s t
    = if !(scEq s t)
         then pure True
         else smallerArg True big s t
smaller inc big s t = smallerArg inc big s t

data SCVar : Type where

mkvar : Int -> Value f [<]
mkvar i = VApp EmptyFC Bound (MN "scv" i) [<] (pure Nothing)

nextVar : {auto c : Ref SCVar Int} -> Core (Value f [<])
nextVar
    = do v <- get SCVar
         put SCVar (v + 1)
         pure (mkvar v)

findSC : {auto c : Ref Ctxt Defs} ->
         {auto v : Ref SCVar Int} ->
         Guardedness ->
         List (Nat, Glued [<]) -> -- LHS args and their position
         Glued [<] -> -- definition. No expanding to NF, we want to check
                      -- the program as written (plus tcinlines)
         Core (List SCCall)

-- Expand the size change argument list with 'Nothing' to match the given
-- arity (i.e. the arity of the function we're calling) to ensure that
-- it's noted that we don't know the size change relationship with the
-- extra arguments.
expandToArity : Nat -> List (Maybe (Nat, SizeChange)) ->
                List (Maybe (Nat, SizeChange))
expandToArity Z xs = xs
expandToArity (S k) (x :: xs) = x :: expandToArity k xs
expandToArity (S k) [] = Nothing :: expandToArity k []

-- if the argument is an 'assert_smaller', return the thing it's smaller than
asserted : Name -> Glued [<] -> Core (Maybe (Glued [<]))
asserted aSmaller (VApp _ nt fn [<_, _, (_, _, b), _] _)
     = if fn == aSmaller
          then Just <$> b
          else pure Nothing
asserted _ _ = pure Nothing

-- Calculate the size change for the given argument.
-- i.e., return the size relationship of the given argument with an entry
-- in 'pats'; the position in 'pats' and the size change.
-- Nothing if there is no relation with any of them.
mkChange : {auto c : Ref Ctxt Defs} ->
           Name ->
           (pats : List (Nat, Glued [<])) ->
           (arg : Glued [<]) ->
           Core (Maybe (Nat, SizeChange))
mkChange aSmaller [] arg = pure Nothing
mkChange aSmaller ((i, parg) :: pats) arg
    = if !(scEq arg parg)
         then pure (Just (i, Same))
         else do s <- smaller False !(asserted aSmaller arg) arg parg
                 if s then pure (Just (i, Smaller))
                      else mkChange aSmaller pats arg

findSCcall : {auto c : Ref Ctxt Defs} ->
             {auto v : Ref SCVar Int} ->
             Guardedness ->
             List (Nat, Glued [<]) ->
             FC -> Name -> Nat -> List (Glued [<]) ->
             Core (List SCCall)
findSCcall g pats fc fn_in arity args
        -- Under 'assert_total' we assume that all calls are fine, so leave
        -- the size change list empty
      = do defs <- get Ctxt
           fn <- getFullName fn_in
           log "totality.termination.sizechange" 10 $ "Looking under "
                  ++ show fn
           aSmaller <- resolved (gamma defs) (NS builtinNS (UN $ Basic "assert_smaller"))
           if fn == NS builtinNS (UN $ Basic "assert_total")
              then pure []
              else
               do scs <- traverse (findSC g pats) args
                  pure ([MkSCCall fn
                           (expandToArity arity
                                !(traverse (mkChange aSmaller pats) args))]
                           ++ concat scs)

-- Substitute a name with what we know about it.
-- We assume that the name has come from a case pattern, which means we're
-- not going to have to look under binders.
-- We also assume that (despite the 'Glued') it's always a VDCon or VDelay
-- therefore no need to expand apps.
substNameInVal : Name -> Glued vars -> Glued vars -> Core (Glued vars)
-- Only interested in Bound names (that we just made) and so we only need
-- to check the index
substNameInVal (MN _ i') rep tm@(VApp _ Bound (MN _ i) _ _)
    = if i == i' then pure rep else pure tm
substNameInVal n rep (VDCon fc cn t a sp)
    = pure $ VDCon fc cn t a !(substNameInSpine sp)
  where
    substNameInSpine : Spine vars -> Core (Spine vars)
    substNameInSpine [<] = pure [<]
    substNameInSpine (rest :< (fc, c, arg))
        = do rest' <- substNameInSpine rest
             pure (rest' :< (fc, c, substNameInVal n rep !arg))
substNameInVal n rep (VDelay fc r t v)
    = pure $ VDelay fc r !(substNameInVal n rep t) !(substNameInVal n rep v)
substNameInVal n rep tm = pure tm

replaceInArgs : Name -> Glued [<] ->
                List (Nat, Glued [<]) -> Core (List (Nat, Glued [<]))
replaceInArgs v tm [] = pure []
-- -- Don't copy if there's no substitution done!
replaceInArgs v tm ((n, arg) :: args)
    = do arg' <- substNameInVal v tm arg
         if !(scEq arg arg')
            then pure $ (n, arg) :: !(replaceInArgs v tm args)
            else pure $ (n, arg) :: (n, arg') :: !(replaceInArgs v tm args)

expandForced : List (Glued [<], Glued [<]) ->
               List (Nat, Glued [<]) -> Core (List (Nat, Glued [<]))
expandForced [] args = pure args
-- Only useful if the equality evaluated to a bound name that we know about
expandForced ((VApp _ Bound n _ _, tm) :: fs) args
    = expandForced fs !(replaceInArgs n tm args)
expandForced (_ :: fs) args = expandForced fs args

findSCscope : {auto c : Ref Ctxt Defs} ->
              {auto v : Ref SCVar Int} ->
         Guardedness ->
         List (Nat, Glued [<]) -> -- LHS args and their position
         Maybe Name -> -- variable we're splitting on (if it is a variable)
         FC -> Glued [<] ->
         (args : _) -> VCaseScope args [<] -> -- case alternative
         Core (List SCCall)
findSCscope g args var fc pat [<] sc
   = do (eqs, rhs) <- sc
        findSC g !(expandForced eqs
                    !(maybe (pure args)
                            (\v => replaceInArgs v pat args) var))
                 rhs
findSCscope g args var fc pat (cargs :< (c, xn)) sc
   = do varg <- nextVar
        pat' <- the (Core (Glued [<])) $ case pat of
                  VDCon vfc n t a sp =>
                      pure (VDCon vfc n t a (sp :< (fc, c, pure varg)))
                  _ => throw (InternalError "Not a data constructor in findSCscope")
        findSCscope g args var fc pat' cargs (sc (pure varg))

findSCalt : {auto c : Ref Ctxt Defs} ->
            {auto v : Ref SCVar Int} ->
         Guardedness ->
         List (Nat, Glued [<]) -> -- LHS args and their position
         Maybe Name -> -- variable we're splitting on (if it is a variable)
         VCaseAlt [<] -> -- case alternative
         Core (List SCCall)
findSCalt g args var (VConCase fc n t cargs sc)
    = findSCscope g args var fc (VDCon fc n t (length cargs) [<]) _ sc
findSCalt g args var (VDelayCase fc ty arg tm)
    = do targ <- nextVar
         varg <- nextVar
         let pat = VDelay fc LUnknown targ varg
         (eqs, rhs) <- tm (pure targ) (pure varg)
         findSC g !(expandForced eqs
                     !(maybe (pure args)
                             (\v => replaceInArgs v pat args) var))
                  rhs
findSCalt g args var (VConstCase fc c tm)
    = findSC g !(maybe (pure args)
                       (\v => replaceInArgs v (VPrimVal fc c) args) var)
               tm
findSCalt g args var (VDefaultCase fc tm) = findSC g args tm

findSCspine : {auto c : Ref Ctxt Defs} ->
         {auto v : Ref SCVar Int} ->
         Guardedness ->
         List (Nat, Glued [<]) -> -- LHS args and their position
         Spine [<] ->
         Core (List SCCall)
findSCspine g pats [<] = pure []
findSCspine g pats (sp :< (_, _, v))
    = do vCalls <- findSC g pats !v
         spCalls <- findSCspine g pats sp
         pure (vCalls ++ spCalls)

findSCapp : {auto c : Ref Ctxt Defs} ->
            {auto v : Ref SCVar Int} ->
         Guardedness ->
         List (Nat, Glued [<]) -> -- LHS args and their position
         Glued [<] -> -- dealing with cases where this is an application
                      -- of some sort
         Core (List SCCall)
findSCapp InDelay pats (VDCon fc n t a sp)
    = findSCspine InDelay pats sp
findSCapp InDelay pats (VApp fc Func n sp _)
    = -- Just check the arguments, they call is okay because we're in a Delay
      -- immediately under a constructor
      findSCspine Unguarded pats sp
findSCapp g pats (VApp fc Func fn sp _)
    = do args <- traverseSnocList (snd . snd) sp
         defs <- get Ctxt
         Just ty <- lookupTyExact fn (gamma defs)
            | Nothing => do
                log "totality" 50 $ "Lookup failed"
                findSCcall Unguarded pats fc fn 0 (cast args)
         g' <- allGuarded fn
         arity <- getArity [<] ty
         findSCcall g' pats fc fn arity (cast args)
  where
    allGuarded : Name -> Core Guardedness
    allGuarded n
        = do defs <- get Ctxt
             Just gdef <- lookupCtxtExact n (gamma defs)
                  | Nothing => pure Unguarded
             if AllGuarded `elem` flags gdef
                then case g of
                          InDelay => pure InDelay
                          Toplevel => pure Guarded
                          _ => pure Unguarded
                else pure Unguarded
findSCapp Guarded pats (VDCon fc n t a sp)
    = findSCspine Guarded pats sp
findSCapp Toplevel pats (VDCon fc n t a sp)
    = findSCspine Guarded pats sp
findSCapp g pats tm = pure [] -- not an application (TODO: VTCon)

-- If we're Guarded and find a Delay, continue with the argument as InDelay
findSC g args (VLam fc x c p ty sc)
    = do v <- nextVar
         findSC g args !(sc (pure v))
findSC g args (VBind fc n b sc)
    = do v <- nextVar
         pure $ !(findSCbinder b) ++ !(findSC g args !(sc (pure v)))
  where
      findSCbinder : Binder (Glued [<]) -> Core (List SCCall)
      findSCbinder (Let _ c val ty) = findSC Unguarded args val
      findSCbinder _ = pure []
findSC Guarded pats (VDelay _ LInf _ tm)
    = findSC InDelay pats tm
findSC g pats (VDelay _ _ _ tm)
    = findSC g pats tm
findSC g pats (VForce _ _ v sp)
    = do vCalls <- findSC g pats v
         spCalls <- findSCspine Unguarded pats sp
         pure (vCalls ++ spCalls)
findSC g args (VCase fc ct c (VApp _ Bound n [<] _) scTy alts)
    = do altCalls <- traverse (findSCalt g args (Just n)) alts
         pure (concat altCalls)
findSC g args (VCase fc ct c sc scTy alts)
    = do altCalls <- traverse (findSCalt g args Nothing) alts
         scCalls <- findSC Unguarded args (asGlued sc)
         pure (scCalls ++ concat altCalls)
findSC g pats tm = findSCapp g pats tm

findSCTop : {auto c : Ref Ctxt Defs} ->
            {auto v : Ref SCVar Int} ->
            Nat -> List (Nat, Glued [<]) -> Glued [<] -> Core (List SCCall)
findSCTop i args (VLam fc x c p ty sc)
    = do arg <- nextVar
         findSCTop (i + 1) ((i, arg) :: args) !(sc (pure arg))
findSCTop i args def = findSC Toplevel (reverse args) def

getSC : {auto c : Ref Ctxt Defs} ->
        Defs -> Def -> Core (List SCCall)
getSC defs (Function _ tm _ _)
   = do ntm <- nfTotality [<] tm
        logNF "totality.termination.sizechange" 5 "From tree" [<] ntm
        v <- newRef SCVar 0
        sc <- findSCTop 0 [] ntm
        pure $ nub sc
getSC defs _ = pure []

export
calculateSizeChange : {auto c : Ref Ctxt Defs} ->
                      FC -> Name -> Core (List SCCall)
calculateSizeChange loc n
    = do log "totality.termination.sizechange" 5 $ "Calculating Size Change: " ++ show !(toFullNames n)
         defs <- get Ctxt
         Just def <- lookupCtxtExact n (gamma defs)
              | Nothing => undefinedName loc n
         getSC defs (definition def)
