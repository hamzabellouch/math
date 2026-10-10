import OAI.Probability.StrongRayleigh.ObservationNoise
import OAI.Probability.StrongRayleigh.ReferenceObservation

namespace OAI

universe u_1 u_2

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal BigOperators

namespace Problem336AdditiveD139.ObservationNoise

variable {I : Type u_1} {Ω : Type u_2} [MeasurableSpace Ω]
  (μ : ProbabilityMeasure (I → Bool)) (ν : ProbabilityMeasure Ω)

theorem referenceMeasure_eq_referenceLaw :
    referenceMeasure μ (ν : Measure Ω) = ReferenceObservation.law μ ν := rfl

omit [MeasurableSpace Ω] in
theorem history_eq_referenceObservation (B : ℝ≥0 → Ω → ℝ) (u : ℝ≥0)
    (ω : ReferenceObservation.Space I Ω) (i : I) (s : Set.Iic u) :
    history B u ω i s = ReferenceObservation.observation B i s.1 ω := rfl

def realFiltration {B : ℝ≥0 → Ω → ℝ} (hm : ∀ t, Measurable (B t)) :
    Filtration ℝ (inferInstance : MeasurableSpace (ReferenceObservation.Space I Ω)) where
  seq t := historySigma B t.toNNReal
  mono' := fun _ _ huv => historySigma_mono B (Real.toNNReal_mono huv)
  le' t := (measurable_history hm t.toNNReal).comap_le

@[simp] theorem realFiltration_apply {B : ℝ≥0 → Ω → ℝ}
    (hm : ∀ t, Measurable (B t)) (u : ℝ) :
    realFiltration (I := I) hm u = historySigma B u.toNNReal := rfl

lemma toNNReal_add_interval {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) :
    u.toNNReal + (v - u).toNNReal = v.toNNReal := by
  apply NNReal.coe_injective
  simp only [NNReal.coe_add, Real.coe_toNNReal _ hu,
    Real.coe_toNNReal _ (sub_nonneg.mpr huv), Real.coe_toNNReal _ (hu.trans huv)]
  ring

theorem incrementVariance_real {u v : ℝ} (huv : u ≤ v)
    (S : Finset I) (θ : I → ℝ) :
    (incrementVariance (v - u).toNNReal S θ : ℝ) =
      (v - u) * ∑ i ∈ S, θ i ^ 2 := by
  rw [incrementVariance_coe, Real.coe_toNNReal _ (sub_nonneg.mpr huv)]

omit [MeasurableSpace Ω] in
theorem increment_real_eq (B : ℝ≥0 → Ω → ℝ) {u v : ℝ}
    (hu : 0 ≤ u) (huv : u ≤ v) (S : Finset I) (θ : I → ℝ) :
    increment B u.toNNReal (v - u).toNNReal S θ =
      (fun ω : ReferenceObservation.Space I Ω => ∑ i ∈ S, θ i *
        (ReferenceObservation.noise B i v.toNNReal ω -
          ReferenceObservation.noise B i u.toNNReal ω)) := by
  funext ω
  dsimp [increment, ReferenceObservation.noise]
  rw [toNNReal_add_interval hu huv]

theorem real_increment_hasLaw {B : ℝ≥0 → Ω → ℝ}
    (hB : IsPreBrownianReal B (ν : Measure Ω)) (hm : ∀ t, Measurable (B t))
    {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) (S : Finset I) (θ : I → ℝ) :
    HasLaw (fun ω : ReferenceObservation.Space I Ω => ∑ i ∈ S, θ i *
      (ReferenceObservation.noise B i v.toNNReal ω -
        ReferenceObservation.noise B i u.toNNReal ω))
      (gaussianReal 0 (incrementVariance (v - u).toNNReal S θ))
      (ReferenceObservation.law μ ν) := by
  simpa only [increment_real_eq B hu huv S θ,
    referenceMeasure_eq_referenceLaw] using
    increment_hasLaw (μ := μ) hB hm u.toNNReal (v - u).toNNReal S θ

theorem real_increment_indep_history {B : ℝ≥0 → Ω → ℝ}
    (hB : IsPreBrownianReal B (ν : Measure Ω)) (hm : ∀ t, Measurable (B t))
    {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) (S : Finset I) (θ : I → ℝ) :
    IndepFun (fun ω : ReferenceObservation.Space I Ω => ∑ i ∈ S, θ i *
      (ReferenceObservation.noise B i v.toNNReal ω -
        ReferenceObservation.noise B i u.toNNReal ω))
      (history B u.toNNReal) (ReferenceObservation.law μ ν) := by
  simpa only [increment_real_eq B hu huv S θ,
    referenceMeasure_eq_referenceLaw] using
    increment_indep_history (μ := μ) hB hm u.toNNReal (v - u).toNNReal S θ

theorem real_increment_condExp_eq_zero {B : ℝ≥0 → Ω → ℝ}
    (hB : IsPreBrownianReal B (ν : Measure Ω)) (hm : ∀ t, Measurable (B t))
    {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) (S : Finset I) (θ : I → ℝ) :
    (ReferenceObservation.law μ ν)[(fun ω : ReferenceObservation.Space I Ω =>
      ∑ i ∈ S, θ i * (ReferenceObservation.noise B i v.toNNReal ω -
        ReferenceObservation.noise B i u.toNNReal ω)) | realFiltration (I := I) hm u]
      =ᵐ[ReferenceObservation.law μ ν] fun _ => 0 := by
  simpa only [increment_real_eq B hu huv S θ,
    referenceMeasure_eq_referenceLaw, realFiltration_apply] using
    increment_condExp_eq_zero (μ := μ) hB hm u.toNNReal (v - u).toNNReal S θ

end Problem336AdditiveD139.ObservationNoise

end

end OAI
