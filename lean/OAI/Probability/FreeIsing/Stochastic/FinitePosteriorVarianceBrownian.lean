import OAI.Probability.FreeIsing.Brownian.PosteriorField
import OAI.Probability.FreeIsing.Posterior.FinitePosteriorVarianceInverse

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367.FinitePosteriorVariance

open PlantedSymmetry

theorem identDistrib_brownian_spinMean
    {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure (TreeVertex d → IsingSpin)) [IsProbabilityMeasure μ]
    (ν : TreeVertex d → Measure Ω) {B : TreeVertex d → ℝ≥0 → Ω → ℝ}
    (hB : ∀ i, IsPreBrownianReal (B i) (ν i))
    (hmB : ∀ i t, Measurable (B i t))
    (beta : ℝ) (D : Finset (TreeVertex d)) (v : D) (t : ℝ≥0) :
    IdentDistrib
      (fun p : (TreeVertex d → IsingSpin) × (TreeVertex d → Ω) =>
        spinMean beta D v (fun i => (t : ℝ) * spinSign (p.1 i) + B i t (p.2 i)))
      (fun p => spinMean beta D v (observation t p))
      (μ.prod (Measure.infinitePi ν)) (μ.prod (gaussianNoiseLaw (TreeVertex d) t)) := by
  have (i : TreeVertex d) : IsProbabilityMeasure (ν i) :=
    (hB i).isGaussianProcess.isProbabilityMeasure
  let T : ((TreeVertex d → IsingSpin) × (TreeVertex d → Ω)) →
      (TreeVertex d → IsingSpin) × (TreeVertex d → ℝ) :=
    Prod.map id (fun ω i => B i t (ω i))
  have hT : MeasurePreserving T (μ.prod (Measure.infinitePi ν))
      (μ.prod (gaussianNoiseLaw (TreeVertex d) t)) :=
    (MeasurePreserving.id μ).prod (brownian_array_eval_measurePreserving ν hB hmB t)
  have hi : IdentDistrib T id (μ.prod (Measure.infinitePi ν))
      (μ.prod (gaussianNoiseLaw (TreeVertex d) t)) :=
    ⟨hT.measurable.aemeasurable, aemeasurable_id, by simpa using hT.map_eq⟩
  exact hi.comp ((continuous_spinMean beta D v).measurable.comp (measurable_observation t))

theorem brownian_exp_abs_field_moment
    {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] {beta : ℝ} (hbeta : 0 ≤ beta)
    (μ : Measure (TreeVertex d → IsingSpin)) [IsProbabilityMeasure μ]
    (ν : TreeVertex d → Measure Ω) {B : TreeVertex d → ℝ≥0 → Ω → ℝ}
    (hB : ∀ i, IsPreBrownianReal (B i) (ν i))
    (hmB : ∀ i t, Measurable (B i t))
    (D : Finset (TreeVertex d)) (v : D) (t : ℝ≥0) {a : ℝ} (ha : 0 ≤ a) :
    let f := fun p : (TreeVertex d → IsingSpin) × (TreeVertex d → Ω) =>
      Real.exp (a * |Real.artanh (spinMean beta D v
        (fun i => (t : ℝ) * spinSign (p.1 i) + B i t (p.2 i)))|)
    Integrable f (μ.prod (Measure.infinitePi ν)) ∧
      (∫ p, f p ∂μ.prod (Measure.infinitePi ν)) ≤
        2 * Real.exp (a * ((d : ℝ) * beta + t) + (t : ℝ) * a ^ 2 / 2) := by
  have haM : Measurable (fun x : ℝ => Real.exp (a * |Real.artanh x|)) := by
    unfold Real.artanh
    fun_prop
  have hi := (identDistrib_brownian_spinMean μ ν hB hmB beta D v t).comp haM
  exact ⟨hi.integrable_iff.mpr (integrable_exp_abs_field hbeta μ D v t ha),
    hi.integral_eq.trans_le (integral_exp_abs_field_le hbeta μ D v t ha)⟩

theorem brownian_inverse_variance_moment
    {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] {beta : ℝ} (hbeta : 0 ≤ beta)
    (μ : Measure (TreeVertex d → IsingSpin)) [IsProbabilityMeasure μ]
    (ν : TreeVertex d → Measure Ω) {B : TreeVertex d → ℝ≥0 → Ω → ℝ}
    (hB : ∀ i, IsPreBrownianReal (B i) (ν i))
    (hmB : ∀ i t, Measurable (B i t))
    (D : Finset (TreeVertex d)) (v : D) (t : ℝ≥0) (k : ℕ) :
    let f := fun p : (TreeVertex d → IsingSpin) × (TreeVertex d → Ω) =>
      ((1 - (spinMean beta D v
        (fun i => (t : ℝ) * spinSign (p.1 i) + B i t (p.2 i))) ^ 2)⁻¹) ^ k
    Integrable f (μ.prod (Measure.infinitePi ν)) ∧
      (∫ p, f p ∂μ.prod (Measure.infinitePi ν)) ≤
        2 * Real.exp ((2 * (k : ℝ)) * ((d : ℝ) * beta + t) +
          (t : ℝ) * (2 * (k : ℝ)) ^ 2 / 2) := by
  have hm : Measurable (fun x : ℝ => ((1 - x ^ 2)⁻¹) ^ k) := by fun_prop
  have hi := (identDistrib_brownian_spinMean μ ν hB hmB beta D v t).comp hm
  exact ⟨hi.integrable_iff.mpr (integrable_inverse_variance_pow hbeta μ D v t k),
    hi.integral_eq.trans_le (integral_inverse_variance_pow_le hbeta μ D v t k)⟩

end Problem367.FinitePosteriorVariance

end

end OAI
