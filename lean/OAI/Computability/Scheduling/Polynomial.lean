import OAI.Computability.Scheduling.CostBounds

namespace OAI

universe u1 u2

section

namespace ThreeMachine.StackCompiler

def Poly {I : Type u1} (size f : I → ℕ) (d : ℕ) : Prop :=
  Majorized f (fun i => (size i+2)^d)

namespace Poly
variable {I : Type u2} {s f g : I → ℕ} {d e : ℕ}

theorem lift (h : Poly s f d) (hde : d ≤ e) : Poly s f e :=
  h.trans (Majorized.pow_mono (fun _ => by omega) hde)

theorem of_le (h : ∀ i, f i ≤ g i) (hg : Poly s g d) : Poly s f d :=
  (Majorized.of_le h).trans hg

theorem const (s : I → ℕ) (C : ℕ) : Poly s (fun _ => C) 0 :=
  Majorized.const C (fun _ => by simp)

theorem base (s : I → ℕ) : Poly s (fun i => s i+2) 1 := by
  simpa only [Poly,Nat.pow_one] using Majorized.refl (fun i => s i+2)

theorem size (s : I → ℕ) : Poly s s 1 :=
  of_le (fun _ => by omega) (base s)

theorem add (hf : Poly s f d) (hg : Poly s g e) : Poly s (fun i => f i+g i) (max d e) :=
  Majorized.add (hf.lift (le_max_left _ _)) (hg.lift (le_max_right _ _))

theorem mul (hf : Poly s f d) (hg : Poly s g e) : Poly s (fun i => f i*g i) (d+e) := by
  simpa only [Poly,Nat.pow_add] using Majorized.mul hf hg

theorem pow (hf : Poly s f d) (k : ℕ) : Poly s (fun i => (f i)^k) (d*k) := by
  simpa only [Poly,Nat.pow_mul] using Majorized.pow hf k

theorem sub (hf : Poly s f d) (g : I → ℕ) : Poly s (fun i => f i-g i) d :=
  of_le (fun _ => Nat.sub_le _ _) hf

theorem max (hf : Poly s f d) (hg : Poly s g e) : Poly s (fun i => max (f i) (g i)) (max d e) :=
  of_le (fun _ => by omega) (add hf hg)

end Poly
end ThreeMachine.StackCompiler

open Lean in
def polyRuleNames : Array Name := #[
  `OAI.ThreeMachine.StackCompiler.Uniform.time_comp,
  `OAI.ThreeMachine.StackCompiler.Uniform.time_pair,
  `OAI.ThreeMachine.StackCompiler.Uniform.time_congr,
  `OAI.ThreeMachine.StackCompiler.Uniform.time_id,
  `OAI.ThreeMachine.StackCompiler.Uniform.time_fst,
  `OAI.ThreeMachine.StackCompiler.Uniform.time_snd,
  `OAI.ThreeMachine.StackCompiler.Uniform.time_nil,
  `OAI.ThreeMachine.StackCompiler.Uniform.time_unit,
  `OAI.ThreeMachine.StackCompiler.Uniform.time_zero,
  `OAI.ThreeMachine.StackCompiler.Uniform.time_false,
  `OAI.ThreeMachine.StackCompiler.Uniform.time_reinterpret,
  `OAI.ThreeMachine.StackCompiler.Uniform.time_cons,
  `OAI.ThreeMachine.StackCompiler.Uniform.time_choose,
  `OAI.ThreeMachine.StackCompiler.Uniform.time_constant,
  `OAI.ThreeMachine.StackCompiler.Uniform.time_uniform,
  `OAI.ThreeMachine.StackCompiler.Uniform.time_tail,
  `OAI.ThreeMachine.StackCompiler.Uniform.time_none,
  `OAI.ThreeMachine.StackCompiler.Uniform.time_some_le,
  `OAI.ThreeMachine.StackCompiler.Uniform.time_ite_le,
  `OAI.ThreeMachine.StackCompiler.Uniform.time_head?_le,
  `OAI.ThreeMachine.StackCompiler.Uniform.time_length_le,
  `OAI.ThreeMachine.StackCompiler.Uniform.time_drop_le,
  `OAI.ThreeMachine.StackCompiler.Uniform.time_getElem?_le,
  `OAI.ThreeMachine.StackCompiler.Uniform.time_functionGet_le,
  `OAI.ThreeMachine.StackCompiler.Uniform.time_functionGetAny_le,
  `OAI.ThreeMachine.StackCompiler.Uniform.time_functionGetOptionAny_le,
  `OAI.ThreeMachine.StackCompiler.Uniform.time_reindex,
  `OAI.ThreeMachine.StackCompiler.Uniform.time_test_le,
  `OAI.ThreeMachine.StackCompiler.Uniform.time_reverse,
  `OAI.ThreeMachine.StackCompiler.Realizer.time_comp,
  `OAI.ThreeMachine.StackCompiler.Realizer.time_pair,
  `OAI.ThreeMachine.StackCompiler.Realizer.time_congr,
  `OAI.ThreeMachine.StackCompiler.Realizer.time_id,
  `OAI.ThreeMachine.StackCompiler.Realizer.time_fst,
  `OAI.ThreeMachine.StackCompiler.Realizer.time_snd,
  `OAI.ThreeMachine.StackCompiler.Realizer.time_reinterpret,
  `OAI.ThreeMachine.StackCompiler.Realizer.time_choose,
  `OAI.ThreeMachine.StackCompiler.Realizer.time_not_le,
  `OAI.ThreeMachine.StackCompiler.Realizer.time_and_le,
  `OAI.ThreeMachine.StackCompiler.Realizer.time_or_le,
  `OAI.ThreeMachine.StackCompiler.Realizer.time_succ_le,
  `OAI.ThreeMachine.StackCompiler.Realizer.time_test_le,
  `OAI.ThreeMachine.StackCompiler.Realizer.time_add_le,
  `OAI.ThreeMachine.StackCompiler.Realizer.time_sub_le,
  `OAI.ThreeMachine.StackCompiler.Realizer.time_le_le,
  `OAI.ThreeMachine.StackCompiler.Realizer.time_eqNat_le,
  `OAI.ThreeMachine.StackCompiler.Uniform.time_setFilter,
  `OAI.ThreeMachine.StackCompiler.Uniform.time_setEmpty,
  `OAI.ThreeMachine.StackCompiler.Uniform.time_vectorMap,
  `OAI.ThreeMachine.StackCompiler.Uniform.time_vectorMapAny,
  `OAI.ThreeMachine.StackCompiler.Uniform.time_andD_le,
  `OAI.ThreeMachine.StackCompiler.Uniform.time_noEdges,
  `OAI.ThreeMachine.StackCompiler.Uniform.time_stateEq,
  `OAI.ThreeMachine.StackCompiler.Uniform.time_stateCompatible,
  `OAI.ThreeMachine.StackCompiler.Uniform.time_append_le,
  `OAI.ThreeMachine.StackCompiler.Uniform.time_getD_le,
  `OAI.ThreeMachine.StackCompiler.Realizer.time_zero,
  `OAI.ThreeMachine.StackCompiler.Realizer.time_nil,
  `OAI.ThreeMachine.StackCompiler.Realizer.time_cons,
  `OAI.ThreeMachine.StackCompiler.Realizer.time_reverse_le,
  `OAI.ThreeMachine.StackCompiler.Realizer.time_range_le,
  `OAI.ThreeMachine.StackCompiler.Uniform.time_orD_le,
  `OAI.ThreeMachine.StackCompiler.Uniform.time_states,
  `OAI.ThreeMachine.StackCompiler.Uniform.time_blockAppend,
  `OAI.ThreeMachine.StackCompiler.Uniform.time_blockAppendNamed,
  `OAI.ThreeMachine.StackCompiler.Uniform.time_stateAdvance,
  `OAI.ThreeMachine.StackCompiler.Uniform.time_lookup_setEq_le,
  `OAI.ThreeMachine.StackCompiler.Uniform.time_lookup_stateEq_le,
  `OAI.ThreeMachine.StackCompiler.Uniform.time_tryAdvance,
  `OAI.ThreeMachine.StackCompiler.Uniform.time_solve,
  `OAI.ThreeMachine.StackCompiler.Uniform.time_initialMarks,
  `OAI.ThreeMachine.StackCompiler.Uniform.time_markings,
  `OAI.ThreeMachine.StackCompiler.Uniform.time_layerStep,
  `OAI.ThreeMachine.StackCompiler.Uniform.time_getElemD_le,
  `OAI.ThreeMachine.StackCompiler.Uniform.time_matrixRows,
  `OAI.ThreeMachine.StackCompiler.Uniform.time_paddedMatrix,
  `OAI.ThreeMachine.StackCompiler.Realizer.time_triple_le,
  `OAI.ThreeMachine.StackCompiler.Uniform.time_cardinalMap,
  `OAI.ThreeMachine.StackCompiler.Uniform.time_cardinalValue,
  `OAI.ThreeMachine.StackCompiler.Uniform.time_makeUniverse,
  `OAI.ThreeMachine.StackCompiler.Uniform.time_restrictTime,
  `OAI.ThreeMachine.StackCompiler.Uniform.time_scheduleMatrix,
  `OAI.ThreeMachine.StackCompiler.Uniform.time_predecessorCount,
  `OAI.ThreeMachine.StackCompiler.Uniform.time_predecessors,
  `OAI.ThreeMachine.StackCompiler.Uniform.time_rankFromCounts,
  `OAI.ThreeMachine.StackCompiler.Uniform.time_natLT_le,
  `OAI.ThreeMachine.StackCompiler.Uniform.time_finVal,
  `OAI.ThreeMachine.StackCompiler.Uniform.time_thresholdSets,
  `OAI.ThreeMachine.StackCompiler.Uniform.time_triples,
  `OAI.ThreeMachine.StackCompiler.Uniform.time_cones_cons,
  `OAI.ThreeMachine.StackCompiler.Uniform.time_finEmpty,
  `OAI.ThreeMachine.StackCompiler.Uniform.time_finCons,
  `OAI.ThreeMachine.StackCompiler.Uniform.time_assignments_succ,
  `OAI.ThreeMachine.StackCompiler.Uniform.time_atomSets,
  `OAI.ThreeMachine.StackCompiler.Uniform.time_family,
  `OAI.ThreeMachine.StackCompiler.Uniform.time_fullSolveK,
  `OAI.ThreeMachine.StackCompiler.Uniform.time_scheduleMatrixFixed,
  `OAI.ThreeMachine.StackCompiler.Uniform.time_bestMatrixStep,
  `OAI.ThreeMachine.StackCompiler.Uniform.time_functionListOption_le,
  `OAI.ThreeMachine.StackCompiler.Uniform.time_sndFunctionListOption_le,
  `OAI.ThreeMachine.StackCompiler.Uniform.time_binaryValueStep_le,
  `OAI.ThreeMachine.StackCompiler.Uniform.time_binaryLeadingStep_le,
  `OAI.ThreeMachine.StackCompiler.Uniform.time_binaryTakeStep_le,
  `OAI.ThreeMachine.StackCompiler.Realizer.time_pred,
  `OAI.ThreeMachine.StackCompiler.Uniform.time_binaryParse
]

open Lean Meta Elab Tactic in
private def polyCostHead (e : Expr) : Option Name :=
  let as := e.getAppArgs
  if e.getAppFn.isConstOf ``ThreeMachine.StackCompiler.Uniform.time && as.size ≥ 3 then
    as[as.size-3]!.getAppFn.constName?
  else if e.getAppFn.isConstOf ``ThreeMachine.StackCompiler.Realizer.time && as.size ≥ 2 then
    as[as.size-2]!.getAppFn.constName?
  else none

open Lean Meta Elab Tactic in
private def polyExprName (e : Expr) (n : Name) : Bool := e.getAppFn.isConstOf n

open Lean Meta Elab Tactic in
private def synthPoly (fuel : ℕ) (sz x e : Expr) : TacticM (Expr × Expr) := do
  match fuel with
  | 0 => throwError "poly_bound: expression depth exhausted"
  | fuel+1 =>
    let e := e.headBeta
    let fn ← mkLambdaFVars #[x] e
    for decl in (← getLCtx) do
      unless decl.isImplementationDetail do
        let tp ← instantiateMVars decl.type
        if polyExprName tp ``ThreeMachine.StackCompiler.Poly then
          let as := tp.getAppArgs
          if as.size == 4 then
            if ← isDefEq as[1]! sz then
              if ← isDefEq as[2]! fn then
                return (as[3]!,decl.toExpr)
    if !(e.containsFVar x.fvarId!) then
      return (mkNatLit 0, ← mkAppM ``ThreeMachine.StackCompiler.Poly.const #[sz,e])
    let se := mkApp sz x
    if ← isDefEq e se then
      return (mkNatLit 1, ← mkAppM ``ThreeMachine.StackCompiler.Poly.size #[sz])
    let be ← mkAppM ``Nat.add #[se,mkNatLit 2]
    if ← isDefEq e be then
      return (mkNatLit 1, ← mkAppM ``ThreeMachine.StackCompiler.Poly.base #[sz])
    let es := e.getAppArgs
    let isadd := polyExprName e ``Nat.add || polyExprName e ``HAdd.hAdd
    let ismul := polyExprName e ``Nat.mul || polyExprName e ``HMul.hMul
    let issub := polyExprName e ``Nat.sub || polyExprName e ``HSub.hSub
    let ismax := polyExprName e ``Nat.max || polyExprName e ``Max.max
    if es.size ≥ 2 && (isadd || ismul || issub || ismax) then
      let a := es[es.size-2]!
      let b := es[es.size-1]!
      let (d,h) ← synthPoly fuel sz x a
      if issub then
        let g ← mkLambdaFVars #[x] b
        return (d, ← mkAppM ``ThreeMachine.StackCompiler.Poly.sub #[h,g])
      let (_,h') ← synthPoly fuel sz x b
      let nm := if isadd then ``ThreeMachine.StackCompiler.Poly.add
        else if ismul then ``ThreeMachine.StackCompiler.Poly.mul
        else ``ThreeMachine.StackCompiler.Poly.max
      let proof ← mkAppM nm #[h,h']
      let tp ← inferType proof
      return (tp.getAppArgs[3]!,proof)
    if es.size ≥ 2 && (polyExprName e ``Nat.pow || polyExprName e ``HPow.hPow) &&
        !(es[es.size-1]!.containsFVar x.fvarId!) then
      let (_,h) ← synthPoly fuel sz x es[es.size-2]!
      let proof ← mkAppM ``ThreeMachine.StackCompiler.Poly.pow #[h,es[es.size-1]!]
      let tp ← inferType proof
      return (tp.getAppArgs[3]!,proof)
    if es.size == 1 && polyExprName e ``Nat.succ then
      let (_,h) ← synthPoly fuel sz x es[0]!
      let hc ← mkAppM ``ThreeMachine.StackCompiler.Poly.const #[sz,mkNatLit 1]
      let proof ← mkAppM ``ThreeMachine.StackCompiler.Poly.add #[h,hc]
      let tp ← inferType proof
      return (tp.getAppArgs[3]!,proof)
    if polyExprName e ``ThreeMachine.StackCompiler.volume then
      let val := es[es.size-1]!
      let vf ← mkLambdaFVars #[x] val
      let tp ← inferType val
      let ts := tp.getAppArgs
      let finish (pr : Expr) : TacticM (Expr × Expr) := do
        let tp ← inferType pr
        return (tp.getAppArgs[3]!,pr)
      if polyExprName tp ``Nat then
        let (_,h) ← synthPoly fuel sz x val
        return ← finish (← mkAppM `OAI.ThreeMachine.StackCompiler.Poly.volumeNat #[h])
      if polyExprName tp ``Bool then
        return ← finish (← mkAppM `OAI.ThreeMachine.StackCompiler.Poly.volumeBool #[sz,vf])
      if polyExprName tp ``Unit then
        return ← finish (← mkAppM `OAI.ThreeMachine.StackCompiler.Poly.volumeUnit #[sz,vf])
      if polyExprName tp ``Prod then
        let a ← mkAppM ``Prod.fst #[val]
        let b ← mkAppM ``Prod.snd #[val]
        let (_,h) ← synthPoly fuel sz x (← mkAppM ``ThreeMachine.StackCompiler.volume #[a])
        let (_,h') ← synthPoly fuel sz x (← mkAppM ``ThreeMachine.StackCompiler.volume #[b])
        return ← finish (← mkAppM `OAI.ThreeMachine.StackCompiler.Poly.volumeProd #[vf,h,h'])
      let mut dim? : Option Expr := none
      let mut nm := Name.anonymous
      if polyExprName tp ``Fin then
        dim? := some ts[0]!; nm := `OAI.ThreeMachine.StackCompiler.Poly.volumeFin
      if polyExprName tp ``Finset && polyExprName ts[0]! ``Fin then
        dim? := some ts[0]!.getAppArgs[0]!; nm := `OAI.ThreeMachine.StackCompiler.Poly.volumeFinset
      if polyExprName tp ``ThreeMachine.StackCompiler.Universe then
        dim? := some ts[0]!; nm := `OAI.ThreeMachine.StackCompiler.Poly.volumeUniverse
      if polyExprName tp ``ThreeMachine.StackCompiler.Cardinal then
        dim? := some ts[0]!; nm := `OAI.ThreeMachine.StackCompiler.Poly.volumeCardinal
      if polyExprName tp ``ThreeMachine.StackCompiler.Matrix then
        dim? := some ts[0]!; nm := `OAI.ThreeMachine.StackCompiler.Poly.volumeMatrix
      if polyExprName tp ``ThreeMachine.Algorithm.State && polyExprName ts[0]! ``Fin then
        dim? := some ts[0]!.getAppArgs[0]!; nm := `OAI.ThreeMachine.StackCompiler.Poly.volumeState
      if let .forallE _ dom body _ := (← whnf tp) then
        if polyExprName dom ``Fin && polyExprName body ``Bool then
          dim? := some dom.getAppArgs[0]!; nm := `OAI.ThreeMachine.StackCompiler.Poly.volumeBoolVector
        if polyExprName dom ``Fin then
          if let .forallE _ dom₂ body₂ _ := body then
            if polyExprName dom₂ ``Fin && polyExprName body₂ ``Bool then
              if ← isDefEq dom dom₂ then
                dim? := some dom.getAppArgs[0]!; nm := `OAI.ThreeMachine.StackCompiler.Poly.volumeMatrix
      if let some dim := dim? then
        let (_,h) ← synthPoly fuel sz x dim
        return ← finish (← mkAppM nm #[h,vf])
    if let some rh := polyCostHead e then
      for nm in polyRuleNames do
        let saved ← saveState
        try
          let c ← mkConstWithFreshMVarLevels nm
          let (xs,bs,tp) ← forallMetaTelescope (← inferType c)
          let args := tp.getAppArgs
          if args.size < 2 then throwError "not a bound"
          let lhs := args[args.size-2]!
          let rhs := args[args.size-1]!
          unless polyCostHead lhs == some rh do throwError "different routine"
          unless ← isDefEq lhs e do throwError "bound does not match"
          for k in [:xs.size] do
            if ← xs[k]!.mvarId!.isAssigned then pure ()
            else if bs[k]! == BinderInfo.instImplicit then
              let v ← synthInstance (← inferType xs[k]!)
              xs[k]!.mvarId!.assign v
          let p ← instantiateMVars (mkAppN c xs)
          if p.hasMVar then throwError "bound has unresolved hypotheses"
          let rhs ← instantiateMVars rhs
          let (_,h) ← synthPoly fuel sz x rhs
          let p ← if tp.getAppFn.isConstOf ``Eq then mkAppM ``le_of_eq #[p] else pure p
          let p ← mkLambdaFVars #[x] p
          let proof ← mkAppM ``ThreeMachine.StackCompiler.Poly.of_le #[p,h]
          let tp ← inferType proof
          return (tp.getAppArgs[3]!,proof)
        catch _ => saved.restore
      let pos := if e.getAppFn.isConstOf ``ThreeMachine.StackCompiler.Uniform.time then es.size-3 else es.size-2
      let r := es[pos]!
      if let some r' ← unfoldDefinition? r then
        let args := es.set! pos r'.headBeta
        return ← synthPoly fuel sz x (mkAppN e.getAppFn args)
    throwError "poly_bound: no bound for {e}"

open Lean Meta Elab Tactic in
elab "poly_bound" : tactic => do
  let goal ← getMainGoal
  goal.withContext do
    let tp := (← instantiateMVars (← goal.getType)).consumeMData
    unless polyExprName tp ``ThreeMachine.StackCompiler.Poly do
      throwError "poly_bound expects Poly"
    let args := tp.getAppArgs
    let sz := args[1]!
    let fn := args[2]!
    let wanted := args[3]!
    let fty ← inferType fn
    forallTelescopeReducing fty fun xs _ => do
      unless xs.size == 1 do throwError "poly_bound expects unary function"
      let body := (mkApp fn xs[0]!).headBeta
      let (d,h) ← synthPoly 1000 sz xs[0]! body
      let le ← mkFreshExprMVar (← mkAppM ``LE.le #[d,wanted])
      let proof ← mkAppM ``ThreeMachine.StackCompiler.Poly.lift #[h,le]
      goal.assign proof
      replaceMainGoal [le.mvarId!]
  evalTactic (← `(tactic| omega))
end

end OAI
