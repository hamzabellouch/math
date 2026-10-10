import OAI.Probability.InvariantIsing.Arrays.ReplicaProductContinuity

namespace OAI

/-! A bounded continuous conditional residual is zero when all bounded
continuous total-overlap tests annihilate it. -/

noncomputable section

open MeasureTheory IsingPerceptron

namespace InvariantIsing

theorem ae_zero_of_continuous_overlap_tests {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (p : Ω → ℝ) (hp : Measurable p)
    (f : ℝ → ℝ) (hf : Continuous f) {B : ℝ} (hB : 0 ≤ B) (hb : ∀ r, |f r| ≤ B)
    (htest : ∀ Φ : ℝ → ℝ, Continuous Φ → ∀ C : ℝ, 0 ≤ C → (∀ r, |Φ r| ≤ C) →
      (∫ x, Φ (p x) * f (p x) ∂μ) = 0) : ∀ᵐ x ∂μ, f (p x) = 0 := by
  have hi : Integrable (fun x => f (p x) ^ 2) μ := by
    apply integrable_of_measurable_abs_le ((hf.measurable.comp hp).pow_const 2)
    intro x
    rw [abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (hb (p x)) 2
  have hz : (∫ x, f (p x) ^ 2 ∂μ) = 0 := by
    simpa only [pow_two] using htest f hf B hB hb
  have he := (integral_eq_zero_iff_of_nonneg (fun x => sq_nonneg (f (p x))) hi).mp hz
  filter_upwards [he] with x hx
  exact sq_eq_zero_iff.mp hx

end InvariantIsing

end

end OAI
