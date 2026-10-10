import OAI.Computability.Scheduling.PolynomialLists

namespace OAI

section
open Lean in
private def polyCostNames : Array Name := #[
  `OAI.ThreeMachine.StackCompiler.Costs.matrixGet,
  `OAI.ThreeMachine.StackCompiler.Costs.finEq,
  `OAI.ThreeMachine.StackCompiler.Costs.setMem,
  `OAI.ThreeMachine.StackCompiler.Costs.setSubset,
  `OAI.ThreeMachine.StackCompiler.Costs.setEq,
  `OAI.ThreeMachine.StackCompiler.Costs.setInter,
  `OAI.ThreeMachine.StackCompiler.Costs.setDiff,
  `OAI.ThreeMachine.StackCompiler.Costs.setDisjoint,
  `OAI.ThreeMachine.StackCompiler.Costs.noEdgeTest,
  `OAI.ThreeMachine.StackCompiler.Costs.noEdgeRow,
  `OAI.ThreeMachine.StackCompiler.Costs.noEdges,
  `OAI.ThreeMachine.StackCompiler.Costs.stateEqL,
  `OAI.ThreeMachine.StackCompiler.Costs.stateEqM,
  `OAI.ThreeMachine.StackCompiler.Costs.stateEqR,
  `OAI.ThreeMachine.StackCompiler.Costs.stateEqMR,
  `OAI.ThreeMachine.StackCompiler.Costs.stateEqLMR,
  `OAI.ThreeMachine.StackCompiler.Costs.stateEq,
  `OAI.ThreeMachine.StackCompiler.Costs.setCard,
  `OAI.ThreeMachine.StackCompiler.Costs.setUnion,
  `OAI.ThreeMachine.StackCompiler.Costs.stateCandidate,
  `OAI.ThreeMachine.StackCompiler.Costs.stateUpto,
  `OAI.ThreeMachine.StackCompiler.Costs.scLZ,
  `OAI.ThreeMachine.StackCompiler.Costs.scLZR,
  `OAI.ThreeMachine.StackCompiler.Costs.scA,
  `OAI.ThreeMachine.StackCompiler.Costs.scB,
  `OAI.ThreeMachine.StackCompiler.Costs.scC,
  `OAI.ThreeMachine.StackCompiler.Costs.scD,
  `OAI.ThreeMachine.StackCompiler.Costs.scE,
  `OAI.ThreeMachine.StackCompiler.Costs.scF,
  `OAI.ThreeMachine.StackCompiler.Costs.scH,
  `OAI.ThreeMachine.StackCompiler.Costs.scI,
  `OAI.ThreeMachine.StackCompiler.Costs.scJ,
  `OAI.ThreeMachine.StackCompiler.Costs.scIJ,
  `OAI.ThreeMachine.StackCompiler.Costs.scHIJ,
  `OAI.ThreeMachine.StackCompiler.Costs.scFHIJ,
  `OAI.ThreeMachine.StackCompiler.Costs.scEFHIJ,
  `OAI.ThreeMachine.StackCompiler.Costs.scDEFHIJ,
  `OAI.ThreeMachine.StackCompiler.Costs.scCDEFHIJ,
  `OAI.ThreeMachine.StackCompiler.Costs.scBCDEFHIJ,
  `OAI.ThreeMachine.StackCompiler.Costs.scAll,
  `OAI.ThreeMachine.StackCompiler.Costs.stateCompatible,
  `OAI.ThreeMachine.StackCompiler.Costs.blockEmpty,
  `OAI.ThreeMachine.StackCompiler.Costs.blockTriple,
  `OAI.ThreeMachine.StackCompiler.Costs.statesC,
  `OAI.ThreeMachine.StackCompiler.Costs.statesP,
  `OAI.ThreeMachine.StackCompiler.Costs.paddedCell,
  `OAI.ThreeMachine.StackCompiler.Costs.paddedMatrix,
  `OAI.ThreeMachine.StackCompiler.Costs.restrictTimeBound,
  `OAI.ThreeMachine.StackCompiler.Costs.predecessorCell,
  `OAI.ThreeMachine.StackCompiler.Costs.predecessorCount,
  `OAI.ThreeMachine.StackCompiler.Costs.predecessorsBody,
  `OAI.ThreeMachine.StackCompiler.Costs.predecessors,
  `OAI.ThreeMachine.StackCompiler.Costs.rank,
  `OAI.ThreeMachine.StackCompiler.Costs.ranks,
  `OAI.ThreeMachine.StackCompiler.Costs.matrixGetFrame,
  `OAI.ThreeMachine.StackCompiler.Costs.conePred,
  `OAI.ThreeMachine.StackCompiler.Costs.cone,
  `OAI.ThreeMachine.StackCompiler.Costs.triplesE,
  `OAI.ThreeMachine.StackCompiler.Costs.triplesA,
  `OAI.ThreeMachine.StackCompiler.Costs.triplesP,
  `OAI.ThreeMachine.StackCompiler.Costs.triples,
  `OAI.ThreeMachine.StackCompiler.Costs.conesF,
  `OAI.ThreeMachine.StackCompiler.Costs.conesOne,
  `OAI.ThreeMachine.StackCompiler.Costs.cones,
  `OAI.ThreeMachine.StackCompiler.Costs.thresholds,
  `OAI.ThreeMachine.StackCompiler.Costs.atomSetsC,
  `OAI.ThreeMachine.StackCompiler.Costs.atomSetsT,
  `OAI.ThreeMachine.StackCompiler.Costs.atomSetsD,
  `OAI.ThreeMachine.StackCompiler.Costs.atomSets,
  `OAI.ThreeMachine.StackCompiler.Costs.evalTemplatesCanonical,
  `OAI.ThreeMachine.StackCompiler.Costs.familyAssignments,
  `OAI.ThreeMachine.StackCompiler.Costs.familyEval,
  `OAI.ThreeMachine.StackCompiler.Costs.family,
  `OAI.ThreeMachine.StackCompiler.Costs.fullSolve,
  `OAI.ThreeMachine.StackCompiler.Costs.paddedSolve,
  `OAI.ThreeMachine.StackCompiler.Costs.scheduleRestriction,
  `OAI.ThreeMachine.StackCompiler.Costs.scheduleCandidate,
  `OAI.ThreeMachine.StackCompiler.Costs.scheduleMatrixFixed,
  `OAI.ThreeMachine.StackCompiler.Costs.scheduleMatrix,
  `OAI.ThreeMachine.StackCompiler.Costs.edgePairEq,
  `OAI.ThreeMachine.StackCompiler.Costs.edgeAt,
  `OAI.ThreeMachine.StackCompiler.Costs.edgeMatrix,
  `OAI.ThreeMachine.StackCompiler.Costs.nextMatrixCell,
  `OAI.ThreeMachine.StackCompiler.Costs.nextMatrix,
  `OAI.ThreeMachine.StackCompiler.Costs.closureMatrixStep,
  `OAI.ThreeMachine.StackCompiler.Costs.reachMatrix
]

open Lean Meta Elab Tactic in
private def polyAutoCostHead (e : Expr) : Option Name :=
  let e := e.consumeMData
  let as := e.getAppArgs
  if e.getAppFn.isConstOf ``ThreeMachine.StackCompiler.Uniform.time && as.size ≥ 3 then
    as[as.size-3]!.getAppFn.constName?
  else if e.getAppFn.isConstOf ``ThreeMachine.StackCompiler.Realizer.time && as.size ≥ 2 then
    as[as.size-2]!.getAppFn.constName?
  else none

open Lean Meta Elab Tactic in
private def polyAutoExprName (e : Expr) (n : Name) : Bool := e.consumeMData.getAppFn.isConstOf n

open Lean Meta Elab Tactic in
private def withPolyFacts (hs : List Expr) (k : TacticM (Expr × Expr)) : TacticM (Expr × Expr) := do
  match hs with
  | [] => k
  | h::hs =>
    withLetDecl `polyFact (← instantiateMVars (← inferType h)) h fun v => do
      let (a,b) ← withPolyFacts hs k
      return (a.replaceFVar v h,b.replaceFVar v h)

open Lean Meta Elab Tactic in
private def polyAutoRule (e : Expr) : TacticM (Option (Expr × Expr)) := do
  let some rh := polyAutoCostHead e | return none
  let es := e.getAppArgs
  for nm in polyRuleNames do
    if !(← getEnv).contains nm then continue
    let saved ← saveState
    try
      let mut raw := (← getConstInfo nm).type
      while raw.isForall do raw := raw.bindingBody!
      let rargs := raw.getAppArgs
      if rargs.size < 2 then throwError "not a bound"
      unless polyAutoCostHead rargs[rargs.size-2]! == some rh do throwError "different routine"
      let c ← mkConstWithFreshMVarLevels nm
      let (xs,bs,tp) ← forallMetaTelescope (← inferType c)
      let args := tp.getAppArgs
      if args.size < 2 then throwError "not a bound"
      let lhs := args[args.size-2]!
      let rhs := args[args.size-1]!
      unless polyAutoCostHead lhs == some rh do throwError "different routine"
      let lhsArgs := lhs.getAppArgs
      let rpos := if lhs.getAppFn.isConstOf ``ThreeMachine.StackCompiler.Uniform.time then lhsArgs.size-3 else lhsArgs.size-2
      let lr := lhsArgs[rpos]!
      let rr := es[if e.getAppFn.isConstOf ``ThreeMachine.StackCompiler.Uniform.time then es.size-3 else es.size-2]!
      if lr.getAppArgs.size == rr.getAppArgs.size then
        for (a,b) in lr.getAppArgs.zip rr.getAppArgs do
          unless ← isDefEq a b do throwError "routine argument does not match"
      unless ← isDefEq lhs e do throwError "bound does not match"
      for k in [:xs.size] do
        if ← xs[k]!.mvarId!.isAssigned then pure ()
        else if bs[k]! == BinderInfo.instImplicit then
          let v ← synthInstance (← inferType xs[k]!)
          xs[k]!.mvarId!.assign v
      let p ← instantiateMVars (mkAppN c xs)
      if p.hasMVar then throwError "bound has unresolved hypotheses"
      let rhs ← instantiateMVars rhs
      let p ← if tp.getAppFn.isConstOf ``Eq then mkAppM ``le_of_eq #[p] else pure p
      return some (rhs,p)
    catch _ => saved.restore
  return none

open Lean Meta Elab Tactic in
private def polyAutoEstimate (e x : Expr) : TacticM (Option (Expr × Expr × Expr)) := do
  let some rh := polyAutoCostHead e | return none
  let es := e.getAppArgs
  unless e.getAppFn.isConstOf ``ThreeMachine.StackCompiler.Uniform.time do return none
  for nm in polyCostNames do
    if !(← getEnv).contains nm then continue
    let saved ← saveState
    try
      let c ← mkConstWithFreshMVarLevels nm
      let (xs,bs,tp) ← forallMetaTelescope (← inferType c)
      let tp := tp.consumeMData
      unless tp.isAppOf ``ThreeMachine.StackCompiler.Poly do throwError "not polynomial"
      let args := tp.getAppArgs
      let domain := args[0]!
      let sigmaArgs := domain.getAppArgs
      unless domain.isAppOf ``Sigma do throwError "not sigma domain"
      let fn := args[2]!
      withLocalDeclD `p domain fun p => do
        let body := (mkApp fn p).headBeta
        unless polyAutoCostHead body == some rh do throwError "different routine"
        let bs := body.getAppArgs
        unless ← isDefEq bs[bs.size-3]! es[es.size-3]! do throwError "different routine args"
      let v ← mkAppOptM ``Sigma.mk #[some sigmaArgs[0]!,some sigmaArgs[1]!,some es[es.size-2]!,some es.back!]
      for k in [:xs.size] do
        if ← xs[k]!.mvarId!.isAssigned then pure ()
        else if bs[k]! == BinderInfo.instImplicit then
          xs[k]!.mvarId!.assign (← synthInstance (← inferType xs[k]!))
      let h ← instantiateMVars (mkAppN c xs)
      if h.hasMVar then throwError "bound has unresolved hypotheses"
      let g ← mkLambdaFVars #[x] v
      return some (h,g,← instantiateMVars (mkApp args[1]! v))
    catch _ => saved.restore
  return none

open Lean Meta Elab Tactic in
private def polyAutoDegree (p : Expr) : TacticM Expr := do
  let tp := (← instantiateMVars (← inferType p)).consumeMData
  let tp ← withReducible <| whnf tp
  if tp.isAppOfArity ``ThreeMachine.StackCompiler.Poly 4 then
    return tp.getAppArgs[3]!

  throwError "poly_auto: unexpected result type {tp} of {p}"

open Lean Meta Elab Tactic in
private def synthPolyAuto (cache : IO.Ref (Std.HashMap (Expr × Expr × Expr) (Expr × Expr))) (fuel : ℕ) (sz x e : Expr) : TacticM (Expr × Expr) := do
  let key := (sz,x,e)
  if let some r := (← cache.get)[key]? then return r
  let result ← (do
   match fuel with
   | 0 => throwError "poly_auto: expression depth exhausted"
   | fuel+1 =>
     let e ← withReducible <| whnf (← deltaExpand e (fun n =>
       [``Function.comp,``ThreeMachine.Algorithm.Block.append,``ThreeMachine.Algorithm.State.advance,
        ``ThreeMachine.Algorithm.State.finish,``ThreeMachine.Algorithm.Block.empty,
        ``ThreeMachine.Algorithm.Block.triple].contains n)).headBeta
     let fn ← mkLambdaFVars #[x] e
     for decl in (← getLCtx) do
       unless decl.isImplementationDetail do
         let tp := (← instantiateMVars decl.type).consumeMData
         if polyAutoExprName tp ``ThreeMachine.StackCompiler.Poly then
           let as := tp.getAppArgs
           if as.size == 4 then
             if ← withReducible <| isDefEq (← deltaExpand as[1]! (· == ``Function.comp)) sz then
               let factFn ← deltaExpand as[2]! (fun n =>
                 [``Function.comp,``ThreeMachine.Algorithm.Block.append,``ThreeMachine.Algorithm.State.advance,
                  ``ThreeMachine.Algorithm.State.finish,``ThreeMachine.Algorithm.Block.empty,
                  ``ThreeMachine.Algorithm.Block.triple].contains n)
               let same ← withReducible <| isDefEq factFn fn
               let factBody ← withReducible <| whnf (mkApp factFn x).headBeta
               let same ← if same then pure true else if
                   e.getAppFn.isConstOf ``ThreeMachine.StackCompiler.volume &&
                   factBody.getAppFn.isConstOf ``ThreeMachine.StackCompiler.volume then

                 if ← withReducible <| isDefEq factBody.getAppArgs.back! e.getAppArgs.back! then
                   withTransparency .all <| isDefEq factFn fn
                 else pure false
               else pure false
               if same then
                 return (as[3]!,decl.toExpr)
     if !(e.containsFVar x.fvarId!) then
       return (mkNatLit 0, ← mkAppM ``ThreeMachine.StackCompiler.Poly.const #[sz,e])
     let se := mkApp sz x
     if ← withReducible <| isDefEq e se then
       return (mkNatLit 1, ← mkAppM ``ThreeMachine.StackCompiler.Poly.size #[sz])
     let be ← mkAppM ``Nat.add #[se,mkNatLit 2]
     if ← withReducible <| isDefEq e be then
       return (mkNatLit 1, ← mkAppM ``ThreeMachine.StackCompiler.Poly.base #[sz])
     let es := e.getAppArgs
     let isadd := polyAutoExprName e ``Nat.add || polyAutoExprName e ``HAdd.hAdd
     let ismul := polyAutoExprName e ``Nat.mul || polyAutoExprName e ``HMul.hMul
     let issub := polyAutoExprName e ``Nat.sub || polyAutoExprName e ``HSub.hSub
     let ismax := polyAutoExprName e ``Nat.max || polyAutoExprName e ``Max.max
     if es.size ≥ 2 && (isadd || ismul || issub || ismax) then
       let a := es[es.size-2]!
       let b := es[es.size-1]!
       let (d,h) ← synthPolyAuto cache fuel sz x a
       if issub then
         let g ← mkLambdaFVars #[x] b
         return (d, ← mkAppM ``ThreeMachine.StackCompiler.Poly.sub #[h,g])
       let (_,h') ← synthPolyAuto cache fuel sz x b
       let nm := if isadd then ``ThreeMachine.StackCompiler.Poly.add
         else if ismul then ``ThreeMachine.StackCompiler.Poly.mul
         else ``ThreeMachine.StackCompiler.Poly.max
       let proof ← mkAppM nm #[h,h']
       return (← polyAutoDegree proof,proof)
     if e.isAppOfArity ``ite 5 then
       let pf ← mkLambdaFVars #[x] es[1]!
       let (_,h) ← synthPolyAuto cache fuel sz x es[3]!
       let (_,h') ← synthPolyAuto cache fuel sz x es[4]!
       let proof ← mkAppM ``ThreeMachine.StackCompiler.Poly.iteNat #[pf,h,h']
       return (← polyAutoDegree proof,proof)
     if es.size ≥ 2 && (polyAutoExprName e ``Nat.pow || polyAutoExprName e ``HPow.hPow) &&
         !(es[es.size-1]!.containsFVar x.fvarId!) then
       let (_,h) ← synthPolyAuto cache fuel sz x es[es.size-2]!
       let proof ← mkAppM ``ThreeMachine.StackCompiler.Poly.pow #[h,es[es.size-1]!]
       return (← polyAutoDegree proof,proof)
     if es.size == 1 && polyAutoExprName e ``Nat.succ then
       let (_,h) ← synthPolyAuto cache fuel sz x es[0]!
       let hc ← mkAppM ``ThreeMachine.StackCompiler.Poly.const #[sz,mkNatLit 1]
       let proof ← mkAppM ``ThreeMachine.StackCompiler.Poly.add #[h,hc]
       return (← polyAutoDegree proof,proof)
     if let .proj ``Fin 0 v := e then
       let tp ← inferType v
       let n := tp.getAppArgs[0]!
       let (_,h) ← synthPolyAuto cache fuel sz x n
       let vf ← mkLambdaFVars #[x] v
       let proof ← mkAppM ``ThreeMachine.StackCompiler.Poly.finVal #[h,vf]
       return (← polyAutoDegree proof,proof)
     if e.isAppOfArity ``Fin.val 2 then
       let (_,h) ← synthPolyAuto cache fuel sz x es[0]!
       let vf ← mkLambdaFVars #[x] es[1]!
       let proof ← mkAppM ``ThreeMachine.StackCompiler.Poly.finVal #[h,vf]
       return (← polyAutoDegree proof,proof)
     let block? := match e with
       | .proj ``ThreeMachine.Algorithm.Block 0 b => some b
       | _ => if polyAutoExprName e ``ThreeMachine.Algorithm.Block.length then some es.back! else none
     if let some b := block? then
       let (_,h) ← synthPolyAuto cache fuel sz x (← mkAppM ``ThreeMachine.StackCompiler.volume #[b])
       let bf ← mkLambdaFVars #[x] b
       let pr ← mkAppM ``ThreeMachine.StackCompiler.Poly.blockLength #[bf,h]
       return (← polyAutoDegree pr,pr)
     if polyAutoExprName e ``Finset.card then
       let v ← withReducible <| whnf (← deltaExpand es[es.size-1]! (· == ``Function.comp)).headBeta
       let tp ← withReducible <| whnf (← inferType v)
       let elem ← withReducible <| whnf tp.getAppArgs[0]!
       if polyAutoExprName elem ``Fin then
         let (_,h) ← synthPolyAuto cache fuel sz x elem.getAppArgs[0]!
         let vf ← mkLambdaFVars #[x] v
         let proof ← mkAppM ``ThreeMachine.StackCompiler.Poly.finsetCard #[h,vf]
         return (← polyAutoDegree proof,proof)
     if polyAutoExprName e ``List.length then
       let v ← withReducible <| whnf (← deltaExpand es[es.size-1]! (· == ``Function.comp)).headBeta
       if polyAutoExprName v ``List.nil then
         return (mkNatLit 0, ← mkAppM ``ThreeMachine.StackCompiler.Poly.const #[sz,mkNatLit 0])
       if polyAutoExprName v ``List.cons then
         let va := v.getAppArgs
         let (_,h) ← synthPolyAuto cache fuel sz x (← mkAppM ``List.length #[va.back!])
         let af ← mkLambdaFVars #[x] va[va.size-2]!
         let xf ← mkLambdaFVars #[x] va.back!
         let pr ← mkAppM ``ThreeMachine.StackCompiler.Poly.lengthCons #[af,xf,h]
         return (← polyAutoDegree pr,pr)
       if polyAutoExprName v ``List.tail || polyAutoExprName v ``List.reverse then
         let xs := v.getAppArgs.back!
         let (_,h) ← synthPolyAuto cache fuel sz x (← mkAppM ``List.length #[xs])
         let xf ← mkLambdaFVars #[x] xs
         let nm := if polyAutoExprName v ``List.tail then
           ``ThreeMachine.StackCompiler.Poly.lengthTail else ``ThreeMachine.StackCompiler.Poly.lengthReverse
         let pr ← mkAppM nm #[xf,h]
         return (← polyAutoDegree pr,pr)
       if polyAutoExprName v ``List.take || polyAutoExprName v ``List.drop then
         let va := v.getAppArgs
         let (_,h) ← synthPolyAuto cache fuel sz x (← mkAppM ``List.length #[va.back!])
         let kf ← mkLambdaFVars #[x] va[va.size-2]!
         let xf ← mkLambdaFVars #[x] va.back!
         let nm := if polyAutoExprName v ``List.take then
           ``ThreeMachine.StackCompiler.Poly.lengthTake else ``ThreeMachine.StackCompiler.Poly.lengthDrop
         let pr ← mkAppM nm #[kf,xf,h]
         return (← polyAutoDegree pr,pr)
       if polyAutoExprName v ``List.append || polyAutoExprName v ``HAppend.hAppend || polyAutoExprName v ``Append.append then
         let va := v.getAppArgs
         let a := va[va.size-2]!
         let b := va.back!
         let (_,h) ← synthPolyAuto cache fuel sz x (← mkAppM ``List.length #[a])
         let (_,h') ← synthPolyAuto cache fuel sz x (← mkAppM ``List.length #[b])
         let af ← mkLambdaFVars #[x] a
         let bf ← mkLambdaFVars #[x] b
         let pr ← mkAppM ``ThreeMachine.StackCompiler.Poly.lengthAppend #[af,bf,h,h']
         return (← polyAutoDegree pr,pr)
       if polyAutoExprName v ``List.range then
         let (_,h) ← synthPolyAuto cache fuel sz x v.getAppArgs.back!
         let kf ← mkLambdaFVars #[x] v.getAppArgs.back!
         let pr ← mkAppM ``ThreeMachine.StackCompiler.Poly.lengthRange #[kf,h]
         return (← polyAutoDegree pr,pr)
       if polyAutoExprName v ``List.replicate then
         let va := v.getAppArgs
         let (_,h) ← synthPolyAuto cache fuel sz x va[va.size-2]!
         let kf ← mkLambdaFVars #[x] va[va.size-2]!
         let af ← mkLambdaFVars #[x] va.back!
         let pr ← mkAppM ``ThreeMachine.StackCompiler.Poly.lengthReplicate #[kf,af,h]
         return (← polyAutoDegree pr,pr)
       if polyAutoExprName v ``Option.toList then
         let ofn ← mkLambdaFVars #[x] v.getAppArgs.back!
         let pr ← mkAppOptM ``ThreeMachine.StackCompiler.Poly.lengthOption #[none,some sz,none,some ofn]
         return (← polyAutoDegree pr,pr)
       if polyAutoExprName v ``List.map then
         let (_,h) ← synthPolyAuto cache fuel sz x (← mkAppM ``List.length #[v.getAppArgs.back!])
         let ff ← mkLambdaFVars #[x] v.getAppArgs[v.getAppArgs.size-2]!
         let pr ← mkAppM ``ThreeMachine.StackCompiler.Poly.lengthMap #[ff,h]
         return (← polyAutoDegree pr,pr)
       if polyAutoExprName v ``List.product then
         let vs := v.getAppArgs
         let (_,h) ← synthPolyAuto cache fuel sz x (← mkAppM ``List.length #[vs[vs.size-2]!])
         let (_,h') ← synthPolyAuto cache fuel sz x (← mkAppM ``List.length #[vs.back!])
         let pr ← mkAppM ``ThreeMachine.StackCompiler.Poly.lengthProduct #[h,h']
         return (← polyAutoDegree pr,pr)
       if polyAutoExprName v ``List.filter then
         let (_,h) ← synthPolyAuto cache fuel sz x (← mkAppM ``List.length #[v.getAppArgs.back!])
         let pf ← mkLambdaFVars #[x] v.getAppArgs[v.getAppArgs.size-2]!
         let pr ← mkAppM ``ThreeMachine.StackCompiler.Poly.lengthFilter #[pf,h]
         return (← polyAutoDegree pr,pr)
       if polyAutoExprName v ``List.finRange then
         let (_,h) ← synthPolyAuto cache fuel sz x v.getAppArgs[0]!
         let pr ← mkAppM ``ThreeMachine.StackCompiler.Poly.lengthFinRange #[h]
         return (← polyAutoDegree pr,pr)
       if polyAutoExprName v ``Finset.sort then
         let set := v.getAppArgs[1]!
         let (_,h) ← synthPolyAuto cache fuel sz x (← mkAppM ``Finset.card #[set])
         let sf ← mkLambdaFVars #[x] set
         let pr ← mkAppM ``ThreeMachine.StackCompiler.Poly.lengthSort #[sf,h]
         return (← polyAutoDegree pr,pr)
       if polyAutoExprName v ``List.ofFn then
         let fn := v.getAppArgs.back!
         let (_,h) ← synthPolyAuto cache fuel sz x v.getAppArgs[1]!
         let ff ← mkLambdaFVars #[x] fn
         let pr ← mkAppM ``ThreeMachine.StackCompiler.Poly.lengthOfFn #[ff,h]
         return (← polyAutoDegree pr,pr)
       let vfn ← mkLambdaFVars #[x] (← mkAppM ``ThreeMachine.StackCompiler.volume #[v])
       for decl in (← getLCtx) do
         let dt := (← instantiateMVars decl.type).consumeMData
         if polyAutoExprName dt ``ThreeMachine.StackCompiler.Poly then
           let da := dt.getAppArgs
           if (← withReducible <| isDefEq da[1]! sz) && (← withReducible <| isDefEq da[2]! vfn) then
             let vf ← mkLambdaFVars #[x] v
             let pr ← mkAppM ``ThreeMachine.StackCompiler.Poly.lengthVolume #[vf,decl.toExpr]
             return (← polyAutoDegree pr,pr)
       throwError "poly_auto: no length bound for {v}"
     if polyAutoExprName e ``ThreeMachine.StackCompiler.volume then
       let val ← withReducible <| whnf (← deltaExpand es[es.size-1]! (· == ``Function.comp)).headBeta
       let vf ← mkLambdaFVars #[x] val
       let tp ← withReducible <| whnf (← inferType val)
       let ts := tp.getAppArgs
       let finish (pr : Expr) : TacticM (Expr × Expr) := do
         return (← polyAutoDegree pr,pr)
       if polyAutoExprName val ``List.nil then
         return (mkNatLit 0, ← mkAppM ``ThreeMachine.StackCompiler.Poly.const #[sz,mkNatLit 1])
       if val.isAppOfArity ``ite 5 then
         let vs := val.getAppArgs
         let pf ← mkLambdaFVars #[x] vs[1]!
         let af ← mkLambdaFVars #[x] vs[3]!
         let bf ← mkLambdaFVars #[x] vs[4]!
         let (_,ha) ← synthPolyAuto cache fuel sz x (← mkAppM ``ThreeMachine.StackCompiler.volume #[vs[3]!])
         let (_,hb) ← synthPolyAuto cache fuel sz x (← mkAppM ``ThreeMachine.StackCompiler.volume #[vs[4]!])
         return ← finish (← mkAppM ``ThreeMachine.StackCompiler.Poly.volumeIte #[pf,af,bf,ha,hb])
       if polyAutoExprName val ``ThreeMachine.Algorithm.lookup then
         let vs := val.getAppArgs
         let xs := vs[vs.size-2]!
         let k := vs.back!
         let xf ← mkLambdaFVars #[x] xs
         let kf ← mkLambdaFVars #[x] k
         let (_,h) ← synthPolyAuto cache fuel sz x (← mkAppM ``ThreeMachine.StackCompiler.volume #[xs])
         return ← finish (← mkAppM ``ThreeMachine.StackCompiler.Poly.volumeLookup #[xf,kf,h])
       if polyAutoExprName val ``Option.toList then
         let o := val.getAppArgs.back!
         let ofn ← mkLambdaFVars #[x] o
         let (_,h) ← synthPolyAuto cache fuel sz x (← mkAppM ``ThreeMachine.StackCompiler.volume #[o])
         return ← finish (← mkAppM ``ThreeMachine.StackCompiler.Poly.volumeOptionToList #[ofn,h])
       if polyAutoExprName val ``Option.some then
         let a := val.getAppArgs.back!
         let af ← mkLambdaFVars #[x] a
         let (_,h) ← synthPolyAuto cache fuel sz x (← mkAppM ``ThreeMachine.StackCompiler.volume #[a])
         return ← finish (← mkAppM ``ThreeMachine.StackCompiler.Poly.volumeOptionSome #[af,h])
       if polyAutoExprName val ``Option.map then
         let vs := val.getAppArgs
         let f := vs[vs.size-2]!
         let o := vs.back!
         let ofn ← mkLambdaFVars #[x] o
         let ff ← mkLambdaFVars #[x] f
         let listFn ← mkLambdaFVars #[x] (← mkAppM ``Option.toList #[o])
         let pool ← mkAppM ``ThreeMachine.StackCompiler.Poly.ListPool #[listFn]
         let (_,ho) ← synthPolyAuto cache fuel sz x (← mkAppM ``ThreeMachine.StackCompiler.volume #[o])
         let locals := (← getLCtx).decls.toArray.filterMap (fun d => d)
         let xd ← inferType x
         let hf ← withLocalDeclD `q pool fun q => do
           let root ← mkAppM ``Sigma.fst #[q]
           let item ← mkAppM ``Subtype.val #[← mkAppM ``Sigma.snd #[q]]
           let szNew ← mkLambdaFVars #[q] (mkApp sz root)
           let rootFn ← mkLambdaFVars #[q] root
           let mut hs : Array Expr := #[]
           for decl in locals do
             let dt := (← instantiateMVars decl.type).consumeMData
             if polyAutoExprName dt ``ThreeMachine.StackCompiler.Poly then
               if (← withReducible <| isDefEq dt.getAppArgs[0]! xd) then
                 hs := hs.push (← mkAppM ``ThreeMachine.StackCompiler.Poly.precomp #[decl.toExpr,rootFn])
           let hlist ← mkAppM ``ThreeMachine.StackCompiler.Poly.volumeOptionToList #[ofn,ho]
           hs := hs.push (← mkAppM ``ThreeMachine.StackCompiler.Poly.volumePool #[listFn,hlist])
           let (_,pr) ← withPolyFacts hs.toList do
             synthPolyAuto cache fuel szNew q (← mkAppM ``ThreeMachine.StackCompiler.volume #[mkApp (f.replaceFVar x root) item])
           return pr
         return ← finish (← mkAppOptM ``ThreeMachine.StackCompiler.Poly.volumeOptionMap #[none,some sz,none,none,none,none,some ff,some ofn,some hf])
       if polyAutoExprName val ``Option.none then
         let h ← mkAppM ``ThreeMachine.StackCompiler.Poly.const #[sz,mkNatLit 1]
         return ← finish h
       let blockTime? := match val with
         | .proj ``ThreeMachine.Algorithm.Block 1 b => some b
         | _ => if polyAutoExprName val ``ThreeMachine.Algorithm.Block.time then some val.getAppArgs.back! else none
       if let some b := blockTime? then
         let (_,h) ← synthPolyAuto cache fuel sz x (← mkAppM ``ThreeMachine.StackCompiler.volume #[b])
         let bf ← mkLambdaFVars #[x] b
         return ← finish (← mkAppM ``ThreeMachine.StackCompiler.Poly.blockTime #[bf,h])

       let proj? := match val with
         | .proj ``Prod k p => some (k,p)
         | _ => if polyAutoExprName val ``Prod.fst then some (0,val.getAppArgs.back!)
              else if polyAutoExprName val ``Prod.snd then some (1,val.getAppArgs.back!) else none
       if let some (k,p) := proj? then
         let pf ← mkLambdaFVars #[x] p
         let pv ← mkLambdaFVars #[x] (← mkAppM ``ThreeMachine.StackCompiler.volume #[p])
         for decl in (← getLCtx) do
           let dt := (← instantiateMVars decl.type).consumeMData
           if polyAutoExprName dt ``ThreeMachine.StackCompiler.Poly then
             let ds := dt.getAppArgs
             if (← withReducible <| isDefEq ds[1]! sz) && (← withReducible <| isDefEq ds[2]! pv) then
               return ← finish (← mkAppM (if k == 0 then ``ThreeMachine.StackCompiler.Poly.volumeFst else
                 ``ThreeMachine.StackCompiler.Poly.volumeSnd) #[pf,decl.toExpr])
       if polyAutoExprName val ``Finset.sort then
         let set := val.getAppArgs[1]!
         let (_,h) ← synthPolyAuto cache fuel sz x (← mkAppM ``ThreeMachine.StackCompiler.volume #[set])
         return ← finish h
       if polyAutoExprName val ``List.ofFn then
         let f := val.getAppArgs.back!
         let (_,h) ← synthPolyAuto cache fuel sz x (← mkAppM ``ThreeMachine.StackCompiler.volume #[f])
         return ← finish h
       if polyAutoExprName val ``List.finRange then
         let (_,h) ← synthPolyAuto cache fuel sz x val.getAppArgs[0]!
         return ← finish (← mkAppM ``ThreeMachine.StackCompiler.Poly.volumeFinRange #[h])
       if polyAutoExprName tp ``Nat then
         let (_,h) ← synthPolyAuto cache fuel sz x val
         return ← finish (← mkAppM `OAI.ThreeMachine.StackCompiler.Poly.volumeNat #[h])
       if polyAutoExprName tp ``Bool then
         return ← finish (← mkAppM `OAI.ThreeMachine.StackCompiler.Poly.volumeBool #[sz,vf])
       if polyAutoExprName tp ``Unit || polyAutoExprName tp ``PUnit then
         return ← finish (← mkAppM `OAI.ThreeMachine.StackCompiler.Poly.volumeUnit #[sz,vf])
       if polyAutoExprName tp ``Prod then
         let a ← mkAppM ``Prod.fst #[val]
         let b ← mkAppM ``Prod.snd #[val]
         let (_,h) ← synthPolyAuto cache fuel sz x (← mkAppM ``ThreeMachine.StackCompiler.volume #[a])
         let (_,h') ← synthPolyAuto cache fuel sz x (← mkAppM ``ThreeMachine.StackCompiler.volume #[b])
         return ← finish (← mkAppM `OAI.ThreeMachine.StackCompiler.Poly.volumeProd #[vf,h,h'])
       let mut dim? : Option Expr := none
       let mut nm := Name.anonymous
       if polyAutoExprName tp ``Fin then
         dim? := some ts[0]!; nm := `OAI.ThreeMachine.StackCompiler.Poly.volumeFin
       if polyAutoExprName tp ``Finset && polyAutoExprName ts[0]! ``Fin then
         dim? := some ts[0]!.getAppArgs[0]!; nm := `OAI.ThreeMachine.StackCompiler.Poly.volumeFinset
       if polyAutoExprName tp ``ThreeMachine.StackCompiler.Universe then
         dim? := some ts[0]!; nm := `OAI.ThreeMachine.StackCompiler.Poly.volumeUniverse
       if polyAutoExprName tp ``ThreeMachine.StackCompiler.Cardinal then
         dim? := some ts[0]!; nm := `OAI.ThreeMachine.StackCompiler.Poly.volumeCardinal
       if polyAutoExprName tp ``ThreeMachine.StackCompiler.Matrix then
         dim? := some ts[0]!; nm := `OAI.ThreeMachine.StackCompiler.Poly.volumeMatrix
       if polyAutoExprName tp ``ThreeMachine.Algorithm.State && polyAutoExprName ts[0]! ``Fin then
         dim? := some ts[0]!.getAppArgs[0]!; nm := `OAI.ThreeMachine.StackCompiler.Poly.volumeState
       if polyAutoExprName tp ``ThreeMachine.Algorithm.Block then
         if val.getAppFn.isConstOf ``ThreeMachine.Algorithm.Block.mk then
           let bl ← mkAppM ``ThreeMachine.Algorithm.Block.length #[val]
           let bt ← mkAppM ``ThreeMachine.Algorithm.Block.time #[val]
           let (_,hl) ← synthPolyAuto cache fuel sz x bl
           let (_,ht) ← synthPolyAuto cache fuel sz x (← mkAppM ``ThreeMachine.StackCompiler.volume #[bt])
           return ← finish (← mkAppM ``ThreeMachine.StackCompiler.Poly.volumeBlock #[vf,hl,ht])
       if let .forallE _ dom body _ := (← whnf tp) then
         if polyAutoExprName dom ``Fin && polyAutoExprName body ``Bool then
           dim? := some dom.getAppArgs[0]!; nm := `OAI.ThreeMachine.StackCompiler.Poly.volumeBoolVector
         if polyAutoExprName dom ``Fin then
           if let .forallE _ dom₂ body₂ _ := body then
             if polyAutoExprName dom₂ ``Fin && polyAutoExprName body₂ ``Bool then
               if ← isDefEq dom dom₂ then
                 dim? := some dom.getAppArgs[0]!; nm := `OAI.ThreeMachine.StackCompiler.Poly.volumeMatrix
       if let some dim := dim? then
         let (_,h) ← synthPolyAuto cache fuel sz x dim
         return ← finish (← mkAppM nm #[h,vf])
       if polyAutoExprName tp ``List then
         let (_,hl) ← synthPolyAuto cache fuel sz x (← mkAppM ``List.length #[val])
         let pool ← mkAppM ``ThreeMachine.StackCompiler.Poly.ListPool #[vf]
         let locals := (← getLCtx).decls.toArray.filterMap (fun d => d)
         let xd ← inferType x
         let hv ← withLocalDeclD `q pool fun q => do
           let root ← mkAppM ``Sigma.fst #[q]
           let item ← mkAppM ``Subtype.val #[← mkAppM ``Sigma.snd #[q]]
           let szNew ← mkLambdaFVars #[q] (mkApp sz root)
           let rootFn ← mkLambdaFVars #[q] root
           let mut hs : Array Expr := #[]
           for decl in locals do
             let dt := (← instantiateMVars decl.type).consumeMData
             if polyAutoExprName dt ``ThreeMachine.StackCompiler.Poly then
               if (← withReducible <| isDefEq dt.getAppArgs[0]! xd) then
                 hs := hs.push (← mkAppM ``ThreeMachine.StackCompiler.Poly.precomp #[decl.toExpr,rootFn])
           let (_,pr) ← withPolyFacts hs.toList do
             synthPolyAuto cache fuel szNew q (← mkAppM ``ThreeMachine.StackCompiler.volume #[item])
           return pr
         return ← finish (← mkAppM ``ThreeMachine.StackCompiler.Poly.listVolume #[vf,hl,hv])
       if let .forallE _ dom _ _ := (← whnf tp) then
         if polyAutoExprName dom ``Fin then
           let n := dom.getAppArgs[0]!
           let nf ← mkLambdaFVars #[x] n
           let (_,hn) ← synthPolyAuto cache fuel sz x n
           let pool ← mkAppM ``ThreeMachine.StackCompiler.Poly.FinPool #[nf]
           let locals := (← getLCtx).decls.toArray.filterMap (fun d => d)
           let xd ← inferType x
           let hf ← withLocalDeclD `q pool fun q => do
             let root ← mkAppM ``Sigma.fst #[q]
             let item ← mkAppM ``Sigma.snd #[q]
             let szNew ← mkLambdaFVars #[q] (mkApp sz root)
             let rootFn ← mkLambdaFVars #[q] root
             let mut hs : Array Expr := #[]
             for decl in locals do
               let dt := (← instantiateMVars decl.type).consumeMData
               if polyAutoExprName dt ``ThreeMachine.StackCompiler.Poly then
                 if (← withReducible <| isDefEq dt.getAppArgs[0]! xd) then
                   hs := hs.push (← mkAppM ``ThreeMachine.StackCompiler.Poly.precomp #[decl.toExpr,rootFn])
             let (_,pr) ← withPolyFacts hs.toList do
               synthPolyAuto cache fuel szNew q (← mkAppM ``ThreeMachine.StackCompiler.volume #[mkApp (val.replaceFVar x root) item])
             return pr
           return ← finish (← mkAppM ``ThreeMachine.StackCompiler.Poly.volumeFunction #[vf,hn,hf])
     if let some (h,g,z) ← polyAutoEstimate e x then
       let (_,hs) ← synthPolyAuto cache fuel sz x z
       let proof ← mkAppM ``ThreeMachine.StackCompiler.Poly.reparam #[h,g,hs]
       return (← polyAutoDegree proof,proof)
     if e.getAppFn.isConstOf ``ThreeMachine.StackCompiler.Uniform.time && es.size ≥ 3 then
       let routine := es[es.size-3]!
       let rh := routine.getAppFn.constName?
       let loopNames := #[``ThreeMachine.StackCompiler.Uniform.map,
         ``ThreeMachine.StackCompiler.Uniform.filter, ``ThreeMachine.StackCompiler.Uniform.any,
         ``ThreeMachine.StackCompiler.Uniform.all,
         ``ThreeMachine.StackCompiler.Uniform.filterMap, ``ThreeMachine.StackCompiler.Uniform.firstResult,
         ``ThreeMachine.StackCompiler.Uniform.flatMap, ``ThreeMachine.StackCompiler.Uniform.optionMap]
       if let some k := loopNames.findIdx? (some · == rh) then
         let R := routine.getAppArgs.back!
         unless !(R.containsFVar x.fvarId!) do throwError "dynamic routine"
         let idx := es[es.size-2]!
         let inp := es.back!
         let baseValue ← mkAppM ``Prod.fst #[inp]
         let list ← if k == 7 then mkAppM ``Option.toList #[baseValue] else pure baseValue
         let env ← mkAppM ``Prod.snd #[inp]
         let idxFn ← mkLambdaFVars #[x] idx
         let listFn ← mkLambdaFVars #[x] list
         let envFn ← mkLambdaFVars #[x] env
         let (_,hl) ← synthPolyAuto cache fuel sz x (← mkAppM ``List.length #[list])
         let (_,hx) ← synthPolyAuto cache fuel sz x (← mkAppM ``ThreeMachine.StackCompiler.volume #[list])
         let (_,he) ← synthPolyAuto cache fuel sz x (← mkAppM ``ThreeMachine.StackCompiler.volume #[env])
         let ra := routine.getAppArgs
         let dom ← inferType x
         let pool ← mkAppOptM ``ThreeMachine.StackCompiler.Poly.Pool #[some ra[0]!,some dom,some ra[1]!,some idxFn,some listFn]
         let locals := (← getLCtx).decls.toArray.filterMap (fun d => d)
         let (ht,hv) ← withLocalDeclD `q pool fun q => do
           let root ← mkAppM ``Sigma.fst #[q]
           let item ← mkAppM ``Subtype.val #[← mkAppM ``Sigma.snd #[q]]
           let sub (e : Expr) := e.replaceFVar x root
           let sizeNew ← mkLambdaFVars #[q] (mkApp sz root)
           let rootFn ← mkLambdaFVars #[q] root
           let mut hs : Array Expr := #[]
           for decl in locals do
             let dt := (← instantiateMVars decl.type).consumeMData
             if polyAutoExprName dt ``ThreeMachine.StackCompiler.Poly then
               if (← isDefEq dt.getAppArgs[0]! dom) then
                 let p ← mkAppM ``ThreeMachine.StackCompiler.Poly.precomp #[decl.toExpr,rootFn]
                 hs := hs.push p
           let hp ← mkAppM ``ThreeMachine.StackCompiler.Poly.volumePool #[listFn,hx]
           hs := hs.push hp
           withPolyFacts hs.toList do
             let arg ← mkAppM ``Prod.mk #[item,sub env]
             let cost ← mkAppM ``ThreeMachine.StackCompiler.Uniform.time #[R,sub idx,arg]
             let (_,ht) ← synthPolyAuto cache fuel sizeNew q cost
             if k == 0 || k ≥ 4 then
               let f := (← inferType R).getAppArgs.back!
               let out := mkAppN f #[sub idx,arg]
               let (_,hv) ← synthPolyAuto cache fuel sizeNew q (← mkAppM ``ThreeMachine.StackCompiler.volume #[out])
               return (ht,hv)
             else return (ht,mkNatLit 0)
         let nm := #[``ThreeMachine.StackCompiler.Poly.mapTime,
           ``ThreeMachine.StackCompiler.Poly.filterTime, ``ThreeMachine.StackCompiler.Poly.anyTime,
           ``ThreeMachine.StackCompiler.Poly.allTime, ``ThreeMachine.StackCompiler.Poly.filterMapTime,
           ``ThreeMachine.StackCompiler.Poly.firstResultTime, ``ThreeMachine.StackCompiler.Poly.flatMapTime, ``ThreeMachine.StackCompiler.Poly.optionMapTime][k]!
         let optionFn ← mkLambdaFVars #[x] baseValue
         let hx' ← if k == 7 then do
             let (_,h) ← synthPolyAuto cache fuel sz x (← mkAppM ``ThreeMachine.StackCompiler.volume #[baseValue])
             pure h
           else pure hx
         let pre := if k == 7 then
             #[some ra[0]!,some dom,some sz,some ra[1]!,some ra[2]!,some ra[3]!,some ra[4]!,some ra[5]!,some ra[6]!,
               some idxFn,some envFn,some optionFn,some ra[7]!,some R,none,none,none,none]
           else if k == 0 || k ≥ 4 then
             #[some ra[0]!,some dom,some sz,some ra[1]!,some ra[2]!,some ra[3]!,some ra[4]!,some ra[5]!,some ra[6]!,
               some idxFn,some listFn,some envFn,some ra[7]!,some R,none,none,none,none,none]
           else
             #[some ra[0]!,some dom,some sz,some ra[1]!,some ra[2]!,some ra[3]!,some ra[4]!,
               some idxFn,some listFn,some envFn,some ra[5]!,some R,none,none,none,none]
         let args := pre ++ (if k == 7 then #[some ht,some hx',some he] else #[some hl,some ht,some hx,some he])
         let args := if k == 0 || k ≥ 4 then args.push (some hv) else args
         let proof ← mkAppOptM nm args
         return (← polyAutoDegree proof,proof)
     if e.isApp && (← isDefEq (← inferType e) (mkConst ``Nat)) then
       let f := e.appFn!
       let a := e.appArg!
       let tp ← withReducible <| whnf (← inferType f)
       if let .forallE _ dom body _ := tp then
         if polyAutoExprName dom ``Fin && polyAutoExprName body ``Nat then
           let af ← mkLambdaFVars #[x] a
           let (_,hf) ← synthPolyAuto cache fuel sz x (← mkAppM ``ThreeMachine.StackCompiler.volume #[f])
           let proof ← mkAppM ``ThreeMachine.StackCompiler.Poly.natFunctionApply #[af,hf]
           return (← polyAutoDegree proof,proof)
     if (polyAutoCostHead e).isSome then
       if let some (rhs,p) ← polyAutoRule e then
         let (_,h) ← synthPolyAuto cache fuel sz x rhs
         let p ← mkLambdaFVars #[x] p
         let proof ← mkAppM ``ThreeMachine.StackCompiler.Poly.of_le #[p,h]
         return (← polyAutoDegree proof,proof)
       let pos := if e.getAppFn.isConstOf ``ThreeMachine.StackCompiler.Uniform.time then es.size-3 else es.size-2
       let r := es[pos]!
       if let some r' ← unfoldDefinition? r then
         let r' ← zetaReduce r' (zetaDelta := false)
         let r' ← withReducible <| whnf r'
         let args := es.set! pos r'.headBeta
         return ← synthPolyAuto cache fuel sz x (mkAppN e.getAppFn args)
     throwError "poly_auto: no bound for {e}"
  )
  let (d,p) := result
  let d ← instantiateMVars d
  let d ← if d.hasFVar then pure d else whnf d
  let p ← instantiateMVars p
  let p ← if p.approxDepth > 15 then do
      let tp := (← inferType p).consumeMData
      let args := tp.getAppArgs
      let tp := mkAppN tp.getAppFn (args.set! 3 d)
      mkAuxTheorem tp p
    else pure p
  let result := (d,p)
  cache.modify (·.insert key result)
  return result

open Lean Meta Elab Tactic in
elab "poly_auto" : tactic => do
  let goal ← getMainGoal
  goal.withContext do
    let tp := (← instantiateMVars (← goal.getType)).consumeMData
    unless polyAutoExprName tp ``ThreeMachine.StackCompiler.Poly do
      throwError "poly_auto expects Poly, got {tp}"
    let args := tp.getAppArgs
    let sz := args[1]!
    let fn := args[2]!
    let wanted := args[3]!
    let fty ← inferType fn
    forallTelescopeReducing fty fun xs _ => do
      unless xs.size == 1 do throwError "poly_auto expects unary function"
      let body := (mkApp fn xs[0]!).headBeta.consumeMData
      let cache ← IO.mkRef ({} : Std.HashMap (Expr × Expr × Expr) (Expr × Expr))
      let (d,h) ← synthPolyAuto cache 1000 sz xs[0]! body
      let le ← mkFreshExprMVar (← mkAppM ``LE.le #[d,wanted])
      let proof ← mkAppM ``ThreeMachine.StackCompiler.Poly.lift #[h,le]
      goal.assign proof
      replaceMainGoal [le.mvarId!]
  evalTactic (← `(tactic| first | exact Nat.le_refl _ | assumption | omega | decide))
end

end OAI
