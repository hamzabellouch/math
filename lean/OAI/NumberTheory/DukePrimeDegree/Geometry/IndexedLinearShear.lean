import OAI.NumberTheory.DukePrimeDegree.Geometry.FiniteLinearShear

namespace OAI

/-! # Elementary shears on root-indexed finite products -/

noncomputable section
open MeasureTheory ProbabilityTheory Function
namespace DukePrimeDegree

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def indexedLinearShear (i j : ι) (r : ℝ) (x : ι → ℝ) : ι → ℝ :=
  Function.update x i (x i + r * x j)

omit [Fintype ι] in
lemma measurable_indexedLinearShear (i j : ι) (r : ℝ) :
    Measurable (indexedLinearShear i j r) := by
  apply measurable_pi_iff.mpr
  intro k
  by_cases h : k = i
  · subst k
    have hm : Measurable (fun x : ι → ℝ => x i + r*x j) := by fun_prop
    simpa [indexedLinearShear] using hm
  · simpa [indexedLinearShear,h] using measurable_pi_apply k

private def splitIndex (i : ι) : (ι → ℝ) ≃ᵐ (({j // j ≠ i} → ℝ) × ℝ) :=
  (MeasurableEquiv.piCongrLeft (fun _ : ι => ℝ) (Equiv.optionSubtypeNe i)).symm.trans
    (MeasurableEquiv.piOptionEquivProd (fun _ => ℝ))

omit [Fintype ι] in
private lemma splitIndex_apply (i : ι) (x : ι → ℝ) :
    splitIndex i x = ((fun j => x j.val),x i) := by
  rfl

private lemma splitIndex_preserves (i : ι) (ν : ι → Measure ℝ) [∀ j, SigmaFinite (ν j)] :
    MeasurePreserving (splitIndex i) (Measure.pi ν)
      ((Measure.pi fun j : {j // j ≠ i} => ν j.val).prod (ν i)) := by
  let e := Equiv.optionSubtypeNe i
  let E := MeasurableEquiv.piCongrLeft (fun _ : ι => ℝ) e
  let F := MeasurableEquiv.piOptionEquivProd (fun _ : Option {j // j ≠ i} => ℝ)
  have hE := (measurePreserving_piCongrLeft (α := fun _ : ι => ℝ) ν e).symm E
  have hF : MeasurePreserving F (Measure.pi fun j => ν (e j))
      ((Measure.pi fun j : {j // j ≠ i} => ν j.val).prod (ν i)) := by
    have hi : MeasurePreserving F.symm
        ((Measure.pi fun j : {j // j ≠ i} => ν j.val).prod (ν i))
        (Measure.pi fun j => ν (e j)) :=
      ⟨F.symm.measurable,Measure.pi_map_piOptionEquivProd (fun j => ν (e j))⟩
    exact hi.symm F.symm
  exact hF.comp hE

theorem indexedLinearShear_preserves (i j : ι) (hji : j ≠ i) (r : ℝ)
    (ν : ι → Measure ℝ) [∀ k, SigmaFinite (ν k)]
    (h : ν j = Measure.dirac 0 ∨ ∀ a : ℝ, (ν i).map (fun t => t+a) = ν i) :
    MeasurePreserving (indexedLinearShear i j r) (Measure.pi ν) (Measure.pi ν) := by
  rcases h with h | h
  · have hz : ∀ᵐ x ∂Measure.pi ν, x j = 0 :=
      (Measure.tendsto_eval_ae_ae (μ := ν)).eventually
        (show ∀ᵐ t ∂ν j, t = 0 by simp [h])
    refine ⟨measurable_indexedLinearShear i j r, ?_⟩
    calc
      _ = (Measure.pi ν).map id := Measure.map_congr (hz.mono fun x hx => by
        simp [indexedLinearShear,hx])
      _ = _ := Measure.map_id
  · let E := splitIndex i
    let η := Measure.pi fun k : {k // k ≠ i} => ν k.val
    have hE := splitIndex_preserves i ν
    have hS : MeasurePreserving
        (fun z : ({k // k ≠ i} → ℝ) × ℝ => (z.1,z.2 + r*z.1 ⟨j,hji⟩))
        (η.prod (ν i)) (η.prod (ν i)) :=
      (MeasurePreserving.id η).skew_product
        (measurable_snd.add (measurable_const.mul
          ((measurable_pi_apply (⟨j,hji⟩ : {k // k ≠ i})).comp measurable_fst)))
        (Filter.Eventually.of_forall fun w => h (r*w ⟨j,hji⟩))
    have hp := (hE.symm E).comp (hS.comp hE)
    convert hp using 1
    funext x
    apply E.injective
    simp only [Function.comp_apply,E.apply_symm_apply]
    rw [splitIndex_apply,splitIndex_apply]
    apply Prod.ext
    · funext k
      simp [indexedLinearShear,k.prop]
    · simp [indexedLinearShear]

end DukePrimeDegree

end

end OAI
