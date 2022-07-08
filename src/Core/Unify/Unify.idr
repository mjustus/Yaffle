module Core.Unify.Unify

import Core.Core
import Core.Context
import Core.Context.Log
import Core.TT
import Core.Evaluate
import Core.Unify.SolveMeta
import Core.Unify.State

import Data.List
import Data.SnocList
import Data.Vect

import Libraries.Data.IntMap
import Libraries.Data.NameMap

parameters {auto c : Ref Ctxt Defs}
  export
  setInvertible : FC -> Name -> Core ()
  setInvertible fc n
      = do defs <- get Ctxt
           Just gdef <- lookupCtxtExact n (gamma defs)
                | Nothing => undefinedName fc n
           ignore $ addDef n ({ invertible := True } gdef)

  isDefInvertible : FC -> Int -> Core Bool
  isDefInvertible fc i
      = do defs <- get Ctxt
           Just gdef <- lookupCtxtExact (Resolved i) (gamma defs)
                | Nothing => throw (UndefinedName fc (Resolved i))
           pure (invertible gdef)

third : (s, t, u) -> u
third (x, y, z) = z

parameters {auto c : Ref Ctxt Defs} {auto c : Ref UST UState}
  namespace Value
    export
    unify : {vars : _} ->
            UnifyInfo -> FC -> Env Term vars ->
            Value vars -> Value vars -> Core UnifyResult
    export
    unifyWithLazy : {vars : _} ->
            UnifyInfo -> FC -> Env Term vars ->
            Value vars -> Value vars -> Core UnifyResult

  namespace Term
    export
    unify : {vars : _} ->
            UnifyInfo -> FC -> Env Term vars ->
            Term vars -> Term vars -> Core UnifyResult
    export
    unifyWithLazy : {vars : _} ->
            UnifyInfo -> FC -> Env Term vars ->
            Term vars -> Term vars -> Core UnifyResult

  convertError : {vars : _} ->
            FC -> Env Term vars -> Value vars -> Value vars -> Core a
  convertError loc env x y
      = do defs <- get Ctxt
           throw (CantConvert loc defs env !(quote env x) !(quote env y))

  convertErrorS : {vars : _} ->
            Bool -> FC -> Env Term vars -> Value vars -> Value vars ->
            Core a
  convertErrorS s loc env x y
      = if s then convertError loc env y x
             else convertError loc env x y

  postpone : {vars : _} ->
             FC -> UnifyInfo -> String ->
             Env Term vars -> Value vars -> Value vars -> Core UnifyResult
  postpone loc mode logstr env x y
      = do defs <- get Ctxt
           xtm <- quote env x
           ytm <- quote env y
           logC "unify.postpone" 10 $
                do xf <- toFullNames xtm
                   yf <- toFullNames ytm
                   pure (logstr ++ ": " ++ show xf ++ " =?= " ++ show yf)

           -- If we're blocked because a name is undefined, give up
           checkDefined defs x
           checkDefined defs y

           c <- addConstraint (MkConstraint loc (atTop mode) env xtm ytm)
           log "unify.postpone" 10 $
                   show c ++ " NEW CONSTRAINT " ++ show loc
           logTerm "unify.postpone" 10 "X" xtm
           logTerm "unify.postpone" 10 "Y" ytm
           pure (constrain c)
    where
      checkDefined : Defs -> Value vars -> Core ()
      checkDefined defs (VApp _ _ n _ _)
          = do Just _ <- lookupCtxtExact n (gamma defs)
                    | _ => undefinedName loc n
               pure ()
      checkDefined _ _ = pure ()

      undefinedN : Name -> Core Bool
      undefinedN n
          = do defs <- get Ctxt
               pure $ case !(lookupDefExact n (gamma defs)) of
                    Just (Hole _) => True
                    Just (BySearch _ _ _) => True
                    Just (Guess _ _ _) => True
                    _ => False

  postponeS : {vars : _} ->
              Bool -> FC -> UnifyInfo -> String -> Env Term vars ->
              Value vars -> Value vars ->
              Core UnifyResult
  postponeS s loc mode logstr env x y
      = if s then postpone loc (lower mode) logstr env y x
             else postpone loc mode logstr env x y

  postponePatVar : {vars : _} ->
                   (swaporder : Bool) ->
                   UnifyInfo -> FC -> Env Term vars ->
                   (metaname : Name) -> (metaref : Int) ->
                   (margs : List (RigCount, Value vars)) ->
                   (margs' : Spine vars) ->
                   (soln : Value vars) ->
                   Core UnifyResult
  postponePatVar swap mode fc env mname mref margs margs' tm
      = do let x = VMeta fc mname mref margs margs' (pure Nothing)
           if !(convert env x tm)
              then pure success
              else postponeS swap fc mode "Not in pattern fragment" env
                             x tm

  unifyArgs : {vars : _} ->
              UnifyInfo -> FC -> Env Term vars ->
              List (Value vars) -> List (Value vars) ->
              Core UnifyResult
  unifyArgs mode loc env [] [] = pure success
  unifyArgs mode loc env (cx :: cxs) (cy :: cys)
      = do -- Do later arguments first, since they may depend on earlier
           -- arguments and use their solutions.
           cs <- unifyArgs mode loc env cxs cys
           res <- unify (lower mode) loc env cx cy
           pure (union res cs)
  unifyArgs mode loc env _ _ = ufail loc ""

  unifyIfEq : {vars : _} ->
              (postpone : Bool) ->
              FC -> UnifyInfo -> Env Term vars -> Value vars -> Value vars ->
              Core UnifyResult
  unifyIfEq post loc mode env x y
        = if !(convert env x y)
             then pure success
             else if post
                     then postpone loc mode ("Postponing unifyIfEq " ++
                                                 show (atTop mode)) env x y
                     else convertError loc env x y

  spineToValues : Spine vars -> List (Value vars)
  spineToValues sp = toList (map third sp)

  -- Unify a hole application - we have already checked that the hole is
  -- invertible (i.e. it's a determining argument to a proof search where
  -- it is a constructor or something else invertible in each case)
  unifyHoleApp : {vars : _} ->
                 (swaporder : Bool) ->
                 UnifyInfo -> FC -> Env Term vars ->
                 (metaname : Name) -> (metaref : Int) ->
                 (args : List (RigCount, Value vars)) ->
                 (sp : Spine vars) ->
                 Value vars ->
                 Core UnifyResult

  -- Solve a metavariable application (that is, the name applied the to
  -- args and spine) with the given solution.
  -- Also given the results we got from 'patternEnv' that tells us how to
  -- instantiate the environment in the solution
  solveHole : {newvars, vars : _} ->
              FC -> UnifyInfo -> Env Term vars ->
              (metaname : Name) -> (metaref : Int) ->
              (args : List (RigCount, Value vars)) ->
              (sp : Spine vars) ->
              SnocList (Var newvars) ->
              SubVars newvars vars ->
              (solfull : Term vars) -> -- Original solution
              (soln : Term newvars) -> -- Solution with shrunk environment
              (solnf : Value vars) ->
              Core (Maybe UnifyResult)
  solveHole fc mode env mname mref margs margs' locs submv solfull stm solnf
      = do defs <- get Ctxt
           ust <- get UST
           if solutionHeadSame solnf || inNoSolve mref (noSolve ust)
              then pure $ Just success
              else do Just hdef <- lookupCtxtExact (Resolved mref) (gamma defs)
                           | Nothing => throw (InternalError ("Can't happen: Lost hole " ++ show mname))
                      progress <- tryInstantiate fc mode env mname mref (length margs) hdef (toList locs) solfull stm
                      pure $ toMaybe progress (solvedHole mref)
    where
      inNoSolve : Int -> IntMap () -> Bool
      inNoSolve i ns
          = case lookup i ns of
                 Nothing => False
                 Just _ => True

      -- Only need to check the head metavar is the same, we've already
      -- checked the rest if they are the same (and we couldn't instantiate it
      -- anyway...)
      -- Also the solution is expanded by now (via Evaluate.Value.expand)
      solutionHeadSame : Value vars -> Bool
      solutionHeadSame (VMeta _ _ shead _ _ _) = shead == mref
      solutionHeadSame _ = False

  -- Try to solve 'metaname' applied to all the arguments with the
  -- given solution
  unifyHole : {vars : _} ->
              (swaporder : Bool) ->
              UnifyInfo -> FC -> Env Term vars ->
              FC -> (metaname : Name) -> (metaref : Int) ->
              (args : List (RigCount, Value vars)) ->
              (sp : Spine vars) ->
              (soln : Value vars) ->
              Core UnifyResult
  unifyHole swap mode fc env nfc mname mref args sp tmnf
      = do let margs = cast (map snd args)
           let margs' = map third sp
           let pargs = if isLin margs' then margs else margs ++ margs'
           defs <- get Ctxt
           case !(patternEnv env pargs) of
                Nothing =>
                  do Just hdef <- lookupCtxtExact (Resolved mref) (gamma defs)
                        | _ => postponePatVar swap mode fc env mname mref args sp tmnf
                     let Hole _ = definition hdef
                        | _ => postponePatVar swap mode fc env mname mref args sp tmnf
                     if invertible hdef
                        then unifyHoleApp swap mode fc env mname mref args sp tmnf
                        else postponePatVar swap mode fc env mname mref args sp tmnf
                Just (newvars ** (locs, submv)) =>
                  do Just hdef <- lookupCtxtExact (Resolved mref) (gamma defs)
                         | _ => postponePatVar swap mode fc env mname mref args sp tmnf
                     let Hole _ = definition hdef
                         | _ => postponeS swap fc mode "Delayed hole" env
                                          (VMeta fc mname mref args sp (pure Nothing))
                                          tmnf
                     tm <- quote env tmnf
                     Just tm <- occursCheck fc env mode mname tm
                         | _ => postponeS swap fc mode "Occurs check failed" env
                                          (VMeta fc mname mref args sp (pure Nothing))
                                          tmnf
                     let solveOrElsePostpone : Term newvars -> Core UnifyResult
                         solveOrElsePostpone stm = do
                           mbResult <- solveHole fc mode env mname mref
                                            args sp locs submv
                                            tm stm tmnf
                           flip fromMaybe (pure <$> mbResult) $
                             postponeS swap fc mode "Can't instantiate" env
                                       (VMeta fc mname mref args sp (pure Nothing))
                                       tmnf
                     case shrinkTerm tm submv of
                          Just stm => solveOrElsePostpone stm
                          Nothing =>
                            do tm' <- quote env tmnf
                               case shrinkTerm tm' submv of
                                    Nothing => postponeS swap fc mode "Can't shrink" env
                                                 (VMeta fc mname mref args sp (pure Nothing))
                                                 tmnf
                                    Just stm => solveOrElsePostpone stm

  unifyNoEta : {vars : _} ->
          UnifyInfo -> FC -> Env Term vars ->
          Value vars -> Value vars -> Core UnifyResult
  -- Deal with metavariable cases first
  -- If they're both holes, solve the one with the bigger context
  unifyNoEta mode fc env x@(VMeta fcx nx ix margsx argsx _) y@(VMeta fcy ny iy margsy argsy _)
      = do invx <- isDefInvertible fc ix
           if ix == iy && (invx || umode mode == InSearch)
                               -- Invertible, (from auto implicit search)
                               -- so we can also unify the arguments.
              then unifyArgs mode fc env
                             (map snd margsx ++ spineToValues argsx)
                             (map snd margsy ++ spineToValues argsy)
              else do xvs <- traverse expand (map snd margsx)
                      yvs <- traverse expand (map snd margsy)
                      let xlocs = localsIn xvs
                      let ylocs = localsIn yvs
                      -- Solve the one with the bigger context, and if they're
                      -- equal, the one that's applied to fewest things (because
                      -- then the arguments get substituted in)
                      let xbigger = xlocs > ylocs
                                      || (xlocs == ylocs &&
                                           length argsx <= length argsy)
                      if (xbigger || umode mode == InMatch) && not (pv nx)
                         then unifyHole False mode fc env fcx nx ix margsx argsx y
                         else unifyHole True mode fc env fcy ny iy margsy argsy x
    where
      pv : Name -> Bool
      pv (PV _ _) = True
      pv _ = False

      localsIn : List (Value vars) -> Nat
      localsIn [] = 0
      localsIn (VLocal{} :: xs) = 1 + localsIn xs
      localsIn (_ :: xs) = localsIn xs
  unifyNoEta mode fc env (VMeta fcm n i margs args _) tm
      = unifyHole False mode fc env fcm n i margs args tm
  unifyNoEta mode fc env tm (VMeta fcm n i margs args _)
      = unifyHole True mode fc env fcm n i margs args tm
  -- Now the cases where we're decomposing into smaller problems
  -- (TODO)
  unifyNoEta mode fc env x y
      = unifyIfEq (isDelay x || isDelay y) fc mode env x y
    where
      -- If one of them is a delay, and they're not equal, we'd better
      -- postpone and come back to it so we can insert the implicit
      -- Force/Delay later
      isDelay : Value vars -> Bool
      isDelay (VDelayed{}) = True
      isDelay _ = False

  -- At this point, we know that 'VApp' and 'VMeta' don't reduce further
  unifyWithEta : {vars : _} ->
          UnifyInfo -> FC -> Env Term vars ->
          Value vars -> Value vars -> Core UnifyResult
  -- TODO: eta rules
  unifyWithEta mode fc env x y
      = unifyNoEta mode fc env x y

  -- First, see if we need to evaluate VApp a bit more
  -- Also, if we have two VApps that immediately convert without reduction,
  -- take advantage of that
  unifyExpandApps : {vars : _} ->
          UnifyInfo -> FC -> Env Term vars ->
          Value vars -> Value vars -> Core UnifyResult
  -- If the values convert already, we're done
  unifyExpandApps mode fc env x@(VApp fcx ntx nx spx valx) y@(VApp fcy nty ny spy valy)
      = if nx == ny
           then ?checkArgs
           else do valx' <- expand x
                   valy' <- expand y
                   unifyWithEta mode fc env valx' valy'
  -- Otherwise, make sure the top level thing is expanded (so not a reducible
  -- VApp or VMeta node) then move on
  unifyExpandApps mode fc env x y
      = do x' <- expand x
           y' <- expand y
           unifyWithEta mode fc env x' y'

  unifyVal : {vars : _} ->
          UnifyInfo -> FC -> Env Term vars ->
          Value vars -> Value vars -> Core UnifyResult
  unifyVal mode fc env x y = unifyExpandApps mode fc env x y

  unifyValLazy : {vars : _} ->
          UnifyInfo -> FC -> Env Term vars ->
          Value vars -> Value vars -> Core UnifyResult
  -- TODO: Details of coercions
  unifyValLazy mode fc env x y = unifyVal mode fc env x y

  -- The interesting top level case, for unifying values
  Core.Unify.Unify.Value.unify mode fc env x y
     = unifyVal mode fc env x y

  -- The interesting top level case, for unifying values and inserting laziness
  -- coercions if appropriate
  Core.Unify.Unify.Value.unifyWithLazy mode fc env x y
     = unifyValLazy mode fc env x y

  Core.Unify.Unify.Term.unify umode fc env x y
     = do x' <- nf env x
          y' <- nf env y
          unify umode fc env x' y'

  Core.Unify.Unify.Term.unifyWithLazy umode fc env x y
     = do x' <- nf env x
          y' <- nf env y
          unifyWithLazy umode fc env x' y'
