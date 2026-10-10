import Mathlib
import OAI.Computability.MinUncut.Search.UniformFiniteSum
import OAI.Computability.MinUncut.Estimates.SamplerAssembly
import OAI.Computability.MinUncut.Search.ParameterFields
import OAI.Computability.MinUncut.Encoding.DerivedResolver

namespace OAI

section
syntax "comp_arith" : tactic
open Lean Elab Tactic Meta in
elab_rules : tactic
| `(tactic| comp_arith) => do
  let target ← getMainTarget
  let fn := target.getAppArgs.back!
  let head ← lambdaTelescope fn fun args body => do
    let body ← instantiateMVars body
    if !args.isEmpty && !(args.any fun a => body.containsFVar a.fvarId!) then return `constant
    let name := body.getAppFn.constName?
    let ty ← inferType body
    let rat := (← whnf ty).isConstOf ``Rat
    let n ← match name with
    | some ``HAdd.hAdd => pure (if rat then ``MinUncut.Preprocess.ca_ratAdd else ``MinUncut.Preprocess.ca_add)
    | some ``HMul.hMul => pure (if rat then ``MinUncut.Preprocess.ca_ratMul else ``MinUncut.Preprocess.ca_mul)
    | some ``HSub.hSub => pure (if rat then ``MinUncut.Preprocess.ca_ratSub else ``MinUncut.Preprocess.ca_sub)
    | some ``HDiv.hDiv => pure (if rat then ``MinUncut.Preprocess.ca_ratDiv else ``MinUncut.Preprocess.ca_div)
    | some ``HMod.hMod => pure ``MinUncut.Preprocess.ca_mod
    | some ``HPow.hPow => pure (if rat then ``MinUncut.Preprocess.ca_ratPow else ``MinUncut.Preprocess.ca_pow)
    | some ``Inv.inv => pure ``MinUncut.Preprocess.ca_ratInv
    | some ``Nat.choose => pure ``MinUncut.Preprocess.ca_choose
    | some ``Nat.factorial => pure ``MinUncut.Preprocess.ca_factorial
    | some ``Nat.cast => pure ``MinUncut.Preprocess.ca_ratCast
    | some ``Nat.ceil => pure ``MinUncut.Preprocess.ca_ratCeil
    | some ``And => pure ``MinUncut.Preprocess.ca_and
    | some ``LE.le => pure (if body.getAppArgs[0]!.isConstOf ``Rat then ``MinUncut.Preprocess.ca_ratLe else ``MinUncut.Preprocess.ca_natLe)
    | some ``LT.lt => pure (if body.getAppArgs[0]!.isConstOf ``Rat then ``MinUncut.Preprocess.ca_ratLt else ``MinUncut.Preprocess.ca_natLt)
    | _ => pure `fallback
    return n
  if head == `constant then evalTactic (← `(tactic| exact MinUncut.Preprocess.ca_const _))
  else if head == `fallback then evalTactic (← `(tactic| fun_prop))
  else
    evalTactic (← `(tactic| apply $(mkIdent head)))
    evalTactic (← `(tactic| all_goals comp_arith))

end
section
namespace MinUncut.Preprocess
open MinUncut.Inner MinUncut.Outer MinUncut.FiniteGaussian
@[fun_prop] lemma c_epsilon : Computable (fun p : ℕ × ℕ=>InnerData.epsilon p.1 p.2) := by
  unfold InnerData.epsilon
  exact ca_ratDiv (ca_const 1) (ca_ratMul
    (ca_ratMul (ca_const 40) (ca_ratCast (c_T.comp Computable.fst)))
    (ca_ratAdd (ca_ratCast (ca_pow Computable.snd (ca_const 2))) (ca_const 1)))
@[fun_prop] lemma c_atomConstant : Computable (fun p : ℕ × ℕ × ℕ=>InnerData.atomConstant p.1 p.2.1 p.2.2) := by
  unfold InnerData.atomConstant
  apply ca_mul
  · apply ca_pow <;> fun_prop
  · apply ca_choose
    · apply ca_add
      · apply ca_pow <;> fun_prop
      · fun_prop
    · fun_prop

lemma inner_check_0 : ComputablePred (fun p : ℕ × InnerData =>
    2 ≤ p.2.m) := by comp_arith

lemma inner_check_1 : ComputablePred (fun p : ℕ × InnerData =>
    p.2.k+2 ≤ p.2.n) := by comp_arith

lemma inner_check_2 : ComputablePred (fun p : ℕ × InnerData =>
    1 ≤ p.2.k) := by comp_arith

lemma inner_check_3 : ComputablePred (fun p : ℕ × InnerData =>
    0 < p.2.H) := by comp_arith

lemma inner_check_4 : ComputablePred (fun p : ℕ × InnerData =>
    0 < p.2.A) := by comp_arith

lemma inner_check_5 : ComputablePred (fun p : ℕ × InnerData =>
    0 < p.2.γ) := by comp_arith

lemma inner_check_6 : ComputablePred (fun p : ℕ × InnerData =>
    0 < p.2.p) := by comp_arith

lemma inner_check_7 : ComputablePred (fun p : ℕ × InnerData =>
    p.2.p < 1) := by comp_arith

lemma inner_check_8 : ComputablePred (fun p : ℕ × InnerData =>
    0 < p.2.θ) := by comp_arith

lemma inner_check_9 : ComputablePred (fun p : ℕ × InnerData =>
    p.2.θ < 1) := by comp_arith

lemma inner_check_10 : ComputablePred (fun p : ℕ × InnerData =>
    ((p.2.s:ℚ)+3)*(1+rationalSigma p.1^2)⁻¹ ≤ (p.2.s:ℚ)+2) := by comp_arith

lemma inner_check_11 : ComputablePred (fun p : ℕ × InnerData =>
    ((p.2.s:ℚ)+2)*((1+rationalSigma p.1^2)⁻¹)^(p.2.s+2) ≤ 1/16) := by comp_arith

lemma inner_check_12 : ComputablePred (fun p : ℕ × InnerData =>
    rationalR p.1*p.2.m < (p.2.m-p.2.s).choose 2) := by comp_arith

lemma inner_check_13 : ComputablePred (fun p : ℕ × InnerData =>
    ((p.2.s+rationalR p.1*p.2.m:ℕ):ℚ)*(p.2.k:ℚ)/((p.2.n:ℚ)-1) < (InnerData.epsilon p.1 p.2.m*rationalSigma p.1)^2) := by comp_arith

lemma inner_check_14 : ComputablePred (fun p : ℕ × InnerData =>
    (rationalSigma p.1)⁻¹^2/(p.2.H:ℚ) < InnerData.epsilon p.1 p.2.m) := by comp_arith

lemma inner_check_15 : ComputablePred (fun p : ℕ × InnerData =>
    2*(rationalSigma p.1)⁻¹^2/(p.2.A:ℚ) < InnerData.epsilon p.1 p.2.m) := by comp_arith

lemma inner_check_16 : ComputablePred (fun p : ℕ × InnerData =>
    (p.2.m:ℚ)/((p.2.k:ℚ)+1) < (InnerData.epsilon p.1 p.2.m/(2*(p.2.A:ℚ)))^(2^p.2.m)) := by comp_arith

lemma inner_check_17 : ComputablePred (fun p : ℕ × InnerData =>
    (p.2.H:ℚ)*(p.2.γ+(p.2.H:ℚ)^2/(p.2.A:ℚ)) < InnerData.epsilon p.1 p.2.m^2) := by comp_arith

lemma inner_check_18 : ComputablePred (fun p : ℕ × InnerData =>
    p.2.θ^2+(p.2.m:ℚ)*p.2.p*(p.2.n^p.2.m:ℕ)/(rationalSigma p.1)^2 <
    (InnerData.epsilon p.1 p.2.m^2*(rationalSigma p.1)^2*p.2.γ/(InnerData.atomConstant p.2.s p.2.m p.2.n:ℚ))^2) := by comp_arith

lemma inner_check_computable : ComputablePred (fun p : ℕ × InnerData=>p.2.Check p.1) :=
  ca_and inner_check_0 (ca_and inner_check_1 (ca_and inner_check_2 (ca_and inner_check_3 (ca_and inner_check_4 (ca_and inner_check_5 (ca_and inner_check_6 (ca_and inner_check_7 (ca_and inner_check_8 (ca_and inner_check_9 (ca_and inner_check_10 (ca_and inner_check_11 (ca_and inner_check_12 (ca_and inner_check_13 (ca_and inner_check_14 (ca_and inner_check_15 (ca_and inner_check_16 (ca_and inner_check_17 (inner_check_18))))))))))))))))))

@[fun_prop] lemma c_amplitude : Computable (fun p : ℕ × InnerData=>OuterData.amplitude p.1 p.2) := by
  unfold OuterData.amplitude; comp_arith
@[fun_prop] lemma c_hints : Computable OuterData.hints := by
  unfold OuterData.hints
  apply ca_sub
  · apply ca_mul
    · exact c_innerData_m
    · apply ca_pow
      · exact c_innerData_n
      · apply ca_sub
        · exact c_innerData_m
        · exact ca_const 1
  · exact ca_const 1
@[fun_prop] lemma c_rate : Computable OuterData.rate := by unfold OuterData.rate; fun_prop
lemma c_listBound : Computable (fun p : ℕ × InnerData × OuterData=>OuterData.listBound p.1 p.2.1 p.2.2) := by
  unfold OuterData.listBound; comp_arith
lemma c_radicand : Computable (fun p : InnerData × ℕ × ℕ=>OuterData.radicand p.1 p.2.1 p.2.2) := by
  unfold OuterData.radicand; comp_arith
attribute [fun_prop] c_listBound c_radicand
@[fun_prop] lemma c_oTheta : Computable (fun p : ℕ × InnerData × OuterData=>p.2.1.θ) :=
  c_innerData_θ.comp (Computable.fst.comp Computable.snd)
@[fun_prop] lemma c_oP : Computable (fun p : ℕ × InnerData × OuterData=>p.2.1.p) :=
  c_innerData_p.comp (Computable.fst.comp Computable.snd)
@[fun_prop] lemma c_oB4 : Computable (fun p : ℕ × InnerData × OuterData=>p.2.2.b4) :=
  c_outerData_b4.comp (Computable.snd.comp Computable.snd)
lemma outer_check_0 : ComputablePred (fun p : ℕ × InnerData × OuterData=>0 < p.2.2.u) := by comp_arith
lemma outer_check_1 : ComputablePred (fun p : ℕ × InnerData × OuterData=>0 < p.2.2.b4) := by comp_arith
lemma outer_check_2 : ComputablePred (fun p : ℕ × InnerData × OuterData=>0 < p.2.2.v) := by comp_arith
lemma outer_check_3 : ComputablePred (fun p : ℕ × InnerData × OuterData=>1 ≤ p.2.2.t) := by comp_arith
lemma outer_check_4 : ComputablePred (fun p : ℕ × InnerData × OuterData=>p.2.2.k ≤ p.2.2.t) := by comp_arith
lemma outer_check_5 : ComputablePred (fun p : ℕ × InnerData × OuterData=>OuterData.listBound p.1 p.2.1 p.2.2 < p.2.1.p/4) := by comp_arith
lemma outer_check_6 : ComputablePred (fun p : ℕ × InnerData × OuterData=>(64/(p.2.1.θ^2*rationalSigma p.1^2))*(p.1:ℚ)*p.2.2.b4 < p.2.1.p/4) := by comp_arith
lemma outer_check_7 : ComputablePred (fun p : ℕ × InnerData × OuterData=>OuterData.radicand p.2.1 p.2.2.k p.2.2.t < p.2.2.v^2) := by comp_arith
lemma outer_check_8 : ComputablePred (fun p : ℕ × InnerData × OuterData=>(256/p.2.1.θ^4)*(p.2.2.u^2*OuterData.amplitude p.1 p.2.1^2+p.2.2.v*(OuterData.amplitude p.1 p.2.1+OuterData.amplitude p.1 p.2.1^2/p.2.2.u)^4) < p.2.1.p/2) := by comp_arith
lemma outer_check_computable : ComputablePred (fun p : ℕ × InnerData × OuterData=>p.2.2.Check p.1 p.2.1) :=
  ca_and outer_check_0 (ca_and outer_check_1 (ca_and outer_check_2 (ca_and outer_check_3 (ca_and outer_check_4 (ca_and outer_check_5 (ca_and outer_check_6 (ca_and outer_check_7 (outer_check_8))))))))
lemma c_qError : Computable (fun p : ℕ × ℚ=>qError p.1 p.2) := by unfold qError; comp_arith
attribute [fun_prop] c_qError
@[fun_prop] lemma c_gT : Computable (fun p : ℕ × ℕ × ℚ × ℚ × GridData=>p.2.2.2.2.T) :=
  c_gridData_T.comp (Computable.snd.comp (Computable.snd.comp (Computable.snd.comp Computable.snd)))
@[fun_prop] lemma c_gL : Computable (fun p : ℕ × ℕ × ℚ × ℚ × GridData=>p.2.2.2.2.L) :=
  c_gridData_L.comp (Computable.snd.comp (Computable.snd.comp (Computable.snd.comp Computable.snd)))
@[fun_prop] lemma c_gr : Computable (fun p : ℕ × ℕ × ℚ × ℚ × GridData=>p.2.2.2.2.r) :=
  c_gridData_r.comp (Computable.snd.comp (Computable.snd.comp (Computable.snd.comp Computable.snd)))
@[fun_prop] lemma c_gE : Computable (fun p : ℕ × ℕ × ℚ × ℚ × GridData=>p.2.2.2.1) :=
  Computable.fst.comp (Computable.snd.comp (Computable.snd.comp Computable.snd))
lemma grid_check_0 : ComputablePred (fun p : ℕ × ℕ × ℚ × ℚ × GridData=>1 ≤ p.2.2.2.2.T) := by comp_arith
lemma grid_check_1 : ComputablePred (fun p : ℕ × ℕ × ℚ × ℚ × GridData=>1 ≤ p.2.2.2.2.L) := by comp_arith
lemma grid_check_2 : ComputablePred (fun p : ℕ × ℕ × ℚ × ℚ × GridData=>(p.1:ℚ)/(p.2.2.2.2.T:ℚ)^2 < p.2.2.2.1/4) :=
  ca_ratLt (ca_ratDiv (ca_ratCast Computable.fst) (ca_ratPow (ca_ratCast c_gT) (ca_const 2)))
    (ca_ratDiv c_gE (ca_const 4))
lemma grid_check_3 : ComputablePred (fun p : ℕ × ℕ × ℚ × ℚ × GridData=>2*(p.2.1:ℚ)*p.2.2.1*p.2.2.2.2.T/p.2.2.2.2.L < p.2.2.2.1/4) :=
  ca_ratLt (ca_ratDiv (ca_ratMul (ca_ratMul
    (ca_ratMul (ca_const 2) (ca_ratCast (Computable.fst.comp Computable.snd)))
    (Computable.fst.comp (Computable.snd.comp Computable.snd))) (ca_ratCast c_gT)) (ca_ratCast c_gL))
    (ca_ratDiv c_gE (ca_const 4))
lemma c_gErrorArg : Computable (fun p : ℕ × ℕ × ℚ × ℚ × GridData=>((p.2.2.2.2.T:ℚ)^2/2)) :=
  ca_ratDiv (ca_ratPow (ca_ratCast c_gT) (ca_const 2)) (ca_const 2)
lemma c_gError : Computable (fun p : ℕ × ℕ × ℚ × ℚ × GridData=>qError p.2.2.2.2.r ((p.2.2.2.2.T:ℚ)^2/2)) :=
  (c_qError.comp (c_gr.pair c_gErrorArg)).of_eq (by intro p; rfl)
lemma c_gCoef : Computable (fun p : ℕ × ℕ × ℚ × ℚ × GridData=>2*(p.1:ℚ)*p.2.2.2.2.T) :=
  ca_ratMul (ca_ratMul (ca_const 2) (ca_ratCast Computable.fst)) (ca_ratCast c_gT)
lemma grid_check_4 : ComputablePred (fun p : ℕ × ℕ × ℚ × ℚ × GridData=>2*(p.1:ℚ)*p.2.2.2.2.T*qError p.2.2.2.2.r ((p.2.2.2.2.T:ℚ)^2/2) < p.2.2.2.1/4) :=
  ca_ratLt (ca_ratMul c_gCoef c_gError) (ca_ratDiv c_gE (ca_const 4))
lemma grid_check_computable : ComputablePred (fun p : ℕ × ℕ × ℚ × ℚ × GridData=>p.2.2.2.2.Check p.1 p.2.1 p.2.2.1 p.2.2.2.1) :=
  ca_and grid_check_0 (ca_and grid_check_1 (ca_and grid_check_2 (ca_and grid_check_3 (grid_check_4))))
end MinUncut.Preprocess

end
section
namespace MinUncut.Preprocess
open MinUncut.FiniteGaussian

def gridTail (n : ℕ) : ℕ := n.unpair.2
def gridField (n : ℕ) : ℕ := (n.unpair.1-1).unpair.2
def gridExtract (n : ℕ) : GridData :=
  ⟨gridField (gridTail n),gridField (gridTail (gridTail n)),
    gridField (gridTail (gridTail (gridTail n)))⟩
lemma gridExtract_encode (g : GridData) : gridExtract (oldGridEncode g)=g := by
  simp only [oldGridEncode_eq,gridExtract,gridTail,gridField,Nat.unpair_pair,Nat.add_sub_cancel_right]
lemma gridDecode_eq (n : ℕ) : oldGridDecode n =
    if oldGridEncode (gridExtract n)=n then some (gridExtract n) else none := by
  cases h : oldGridDecode n with
  | none =>
    split
    · next he =>
        have hk := @Encodable.encodek GridData instEncodableGridData (gridExtract n)
        change oldGridDecode (oldGridEncode (gridExtract n))=some (gridExtract n) at hk
        rw [he,h] at hk
        cases hk
    · rfl
  | some g =>
    have he := oldGridDecode_canonical n g h
    have hx : gridExtract n=g := by rw [←he,gridExtract_encode]
    simp only [hx,he,ite_true]

@[fun_prop] lemma c_gridTail : Computable gridTail := Computable.snd.comp Computable.unpair
@[fun_prop] lemma c_gridField : Computable gridField :=
  Computable.snd.comp (Computable.unpair.comp
    (ca_sub (Computable.fst.comp Computable.unpair) (ca_const 1)))
lemma c_gridMk : Computable gridDataEquiv.symm :=
  (Primrec.of_equiv_symm (e:=gridDataEquiv)).to_comp
lemma gridExtract_eq : gridExtract = fun n => gridDataEquiv.symm
    (gridField (gridTail n),gridField (gridTail (gridTail n)),
      gridField (gridTail (gridTail (gridTail n)))) := by
  funext n
  simp only [gridExtract,gridDataEquiv,Equiv.coe_fn_symm_mk]
lemma c_gridExtract₁ : Computable (fun n=>gridField (gridTail n)) :=
  c_gridField.comp c_gridTail
lemma c_gridExtract₂ : Computable (fun n=>gridField (gridTail (gridTail n))) :=
  c_gridExtract₁.comp c_gridTail
lemma c_gridExtract₃ : Computable (fun n=>gridField (gridTail (gridTail (gridTail n)))) :=
  c_gridExtract₂.comp c_gridTail
lemma c_gridExtractPair : Computable (fun n=>(gridField (gridTail n),
    gridField (gridTail (gridTail n)),gridField (gridTail (gridTail (gridTail n))))) :=
  c_gridExtract₁.pair (c_gridExtract₂.pair c_gridExtract₃)
lemma c_gridExtract : Computable gridExtract := by
  rw [gridExtract_eq]
  exact c_gridMk.comp c_gridExtractPair
lemma c_oldGridEncode : Computable oldGridEncode := by
  have hp : Computable₂ Nat.pair := Primrec₂.natPair.to_comp
  rw [show oldGridEncode=(fun g : GridData=>Nat.pair (Nat.pair 0 0+1)
    (Nat.pair (Nat.pair 0 g.T+1) (Nat.pair (Nat.pair 0 g.L+1)
      (Nat.pair (Nat.pair 0 g.r+1) (Nat.pair 0 0))))) from funext oldGridEncode_eq]
  exact hp.comp (ca_const _) (hp.comp (ca_add (hp.comp (ca_const 0) c_gridData_T) (ca_const 1))
    (hp.comp (ca_add (hp.comp (ca_const 0) c_gridData_L) (ca_const 1))
      (hp.comp (ca_add (hp.comp (ca_const 0) c_gridData_r) (ca_const 1)) (ca_const _))))
lemma c_oldGridDecode : Computable oldGridDecode := by
  have he : ComputablePred (fun n=>oldGridEncode (gridExtract n)=n) :=
    (Primrec.eq.computablePred.decide.comp ((c_oldGridEncode.comp c_gridExtract).pair Computable.id)).computablePred
  exact (Computable.cond he.decide (Computable.option_some.comp c_gridExtract) (ca_const none)).of_eq
    (by intro n; simp only [Bool.cond_decide]; exact (gridDecode_eq n).symm)
end MinUncut.Preprocess

end
section
namespace MinUncut.Preprocess
open MinUncut.Inner MinUncut.Outer MinUncut.FiniteGaussian

def parameterJ (K : ℕ) : ℕ := 10*(max K 2)
lemma parameterJ_pos (K : ℕ) : 1≤parameterJ K := by unfold parameterJ; omega
lemma parameterJ_eq (K : ℕ) (hK : 2≤K) : parameterJ K=10*K := by
  unfold parameterJ
  rw [max_eq_left hK]
@[fun_prop] lemma c_parameterJ : Computable parameterJ := by
  have h : Computable (fun K : ℕ=>10*(K+(2-K))) := by fun_prop
  exact h.of_eq (by intro K; unfold parameterJ; congr 1; omega)
lemma inner_exists (K : ℕ) : ∃d : InnerData,d.Check (parameterJ K) :=
  InnerData.check_exists (parameterJ_pos K)
noncomputable def selectedInner (K : ℕ) : InnerData := search inner_exists K
lemma selectedInner_check (K : ℕ) : (selectedInner K).Check (parameterJ K) :=
  search_spec inner_exists K
lemma c_inner_pred : ComputablePred (fun p : ℕ × InnerData=>p.2.Check (parameterJ p.1)) :=
  (inner_check_computable.decide.comp ((c_parameterJ.comp Computable.fst).pair Computable.snd)).computablePred
@[fun_prop] lemma c_selectedInner : Computable selectedInner :=
  computable_search c_inner_pred inner_exists ⟨0,0,0,0,0,0,0,0,0⟩

attribute [local irreducible] selectedInner

lemma outer_exists (K : ℕ) : ∃o : OuterData,o.Check (parameterJ K) (selectedInner K) :=
  OuterData.check_exists (parameterJ_pos K) _ (selectedInner_check K)
noncomputable def selectedOuter (K : ℕ) : OuterData := search outer_exists K
lemma selectedOuter_check (K : ℕ) : (selectedOuter K).Check (parameterJ K) (selectedInner K) :=
  search_spec outer_exists K
lemma c_outer_arguments : Computable (fun p : ℕ × OuterData =>
    (parameterJ p.1,selectedInner p.1,p.2)) := by
  exact (c_parameterJ.comp Computable.fst).pair
    ((c_selectedInner.comp Computable.fst).pair Computable.snd)
lemma c_outer_decide : Computable (fun p : ℕ × OuterData =>
    decide (p.2.Check (parameterJ p.1) (selectedInner p.1))) := by
  have hh : Computable (fun p : ℕ × InnerData × OuterData=>decide (p.2.2.Check p.1 p.2.1)) :=
    outer_check_computable.decide
  exact @Computable.comp (ℕ × OuterData) (ℕ × InnerData × OuterData) Bool _ _ _
    (fun p=>decide (p.2.2.Check p.1 p.2.1)) (fun p=>(parameterJ p.1,selectedInner p.1,p.2)) hh c_outer_arguments
lemma c_outer_pred : ComputablePred (fun p : ℕ × OuterData=>p.2.Check (parameterJ p.1) (selectedInner p.1)) :=
  c_outer_decide.computablePred
@[fun_prop] lemma c_selectedOuter : Computable selectedOuter :=
  computable_search c_outer_pred outer_exists ⟨0,0,0,0,0⟩
noncomputable def selectedParameters (K : ℕ) : Parameters (parameterJ K) :=
  ⟨parameterJ_pos K,selectedInner K,selectedInner_check K,selectedOuter K,selectedOuter_check K⟩

def gridPredicate (x : ℕ × ℕ × ℚ × ℚ) (g : GridData) : Prop :=
  if 0≤x.2.2.1 ∧ 0<x.2.2.2 then g.Check x.1 x.2.1 x.2.2.1 x.2.2.2 else g=⟨0,0,0⟩
instance : DecidableRel gridPredicate := fun _ _=>by unfold gridPredicate; infer_instance
lemma grid_exists (x : ℕ × ℕ × ℚ × ℚ) : ∃g,gridPredicate x g := by
  unfold gridPredicate
  split_ifs with h
  · exact GridData.exists_check x.1 x.2.1 h.1 h.2
  · exact ⟨_,rfl⟩
noncomputable def selectedGrid (x : ℕ × ℕ × ℚ × ℚ) : GridData :=
  searchWith instEncodableGridData grid_exists x
lemma selectedGrid_eq (d S : ℕ) (A ε : ℚ) (hA : 0≤A) (hε : 0<ε) :
    selectedGrid (d,S,A,ε)=GridData.select d S A ε hA hε := by
  unfold selectedGrid searchWith GridData.select
  congr 1
  funext g
  simp only [gridPredicate,hA,hε,and_self,ite_true]
lemma c_grid_valid : ComputablePred (fun x : ℕ × ℕ × ℚ × ℚ=>0≤x.2.2.1 ∧ 0<x.2.2.2) :=
  ca_and (ca_ratLe (ca_const 0) (Computable.fst.comp (Computable.snd.comp Computable.snd)))
    (ca_ratLt (ca_const 0) (Computable.snd.comp (Computable.snd.comp Computable.snd)))
lemma c_grid_pred : ComputablePred (fun p : (ℕ × ℕ × ℚ × ℚ) × GridData=>gridPredicate p.1 p.2) := by
  have hc := grid_check_computable.decide.comp (Computable.fst.comp Computable.fst |>.pair
    ((Computable.fst.comp (Computable.snd.comp Computable.fst)).pair
      ((Computable.fst.comp (Computable.snd.comp (Computable.snd.comp Computable.fst))).pair
        ((Computable.snd.comp (Computable.snd.comp (Computable.snd.comp Computable.fst))).pair Computable.snd))))
  have he : Computable (fun p : (ℕ × ℕ × ℚ × ℚ) × GridData=>decide (p.2=⟨0,0,0⟩)) :=
    ComputablePred.decide ((Primrec.eq.computablePred.decide.comp
      (Computable.snd.pair (ca_const (⟨0,0,0⟩ : GridData)))).computablePred)
  have hh := Computable.cond (c_grid_valid.decide.comp Computable.fst) hc he
  exact ⟨inferInstance,hh.of_eq (by
    intro p
    simp only [gridPredicate,Bool.cond_decide]
    split_ifs <;> rfl)⟩
lemma c_selectedGrid : Computable selectedGrid :=
  computable_searchWith instEncodableGridData c_oldGridDecode c_grid_pred grid_exists ⟨0,0,0⟩
end MinUncut.Preprocess

end

end OAI
