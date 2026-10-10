import OAI.Combinatorics.Progressions.Probability.DensityComparisonComposition

namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

theorem complex_model_l1_le_of_bounded_tests {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (f g : X → ℂ) (hf : Measurable f) (hg : Measurable g)
    (hfi : Integrable f μ) (hgi : Integrable g μ) {ε : ℝ}
    (he : ∀ φ : X → ℂ, Measurable φ → (∀ x, ‖φ x‖ ≤ 1) →
      ‖(∫ x, f x * φ x ∂μ) - ∫ x, g x * φ x ∂μ‖ ≤ ε) :
    (∫ x, ‖f x - g x‖ ∂μ) ≤ ε := by
  let φ := fun x => (starRingEnd ℂ) (f x - g x) / (‖f x - g x‖ : ℂ)
  have hφ : Measurable φ :=
    (Complex.continuous_conj.measurable.comp (hf.sub hg)).div (hf.sub hg).norm.complex_ofReal
  have hbound (x) : ‖φ x‖ ≤ 1 := by
    dsimp only [φ]
    rw [norm_div, RCLike.norm_conj, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _)]
    exact div_self_le_one _
  have hidentity (x) : (f x - g x) * φ x = (‖f x - g x‖ : ℂ) := by
    dsimp only [φ]
    rw [← mul_div_assoc, Complex.mul_conj', ← Complex.ofReal_pow, ← Complex.ofReal_div]
    by_cases h : ‖f x - g x‖ = 0
    · simp [h]
    · rw [pow_two, mul_div_cancel_right₀ _ h]
  have hif := hfi.mul_bdd hφ.aestronglyMeasurable (Filter.Eventually.of_forall hbound)
  have hig := hgi.mul_bdd hφ.aestronglyMeasurable (Filter.Eventually.of_forall hbound)
  have h := he φ hφ hbound
  rw [← integral_sub hif hig] at h
  simp_rw [← sub_mul, hidentity] at h
  rw [integral_complex_ofReal, Complex.norm_real,
    Real.norm_of_nonneg (integral_nonneg (fun x => norm_nonneg _))] at h
  exact h

namespace FiniteProbabilityWeights

theorem complexMean_integral {Y X : Type*} [Fintype Y] [MeasurableSpace X]
    (law : FiniteProbabilityWeights Y) (μ : Measure X) (f : Y → X → ℂ)
    (hf : ∀ y, Integrable (f y) μ) :
    law.complexMean (fun y => ∫ x, f y x ∂μ) =
      ∫ x, law.complexMean (fun y => f y x) ∂μ := by
  simp only [complexMean]
  rw [integral_finsetSum _ (fun y _ => (hf y).const_mul _)]
  simp only [integral_const_mul]

theorem mean_density_test_integral {Y X : Type*} [Fintype Y] [MeasurableSpace X]
    (law : FiniteProbabilityWeights Y) (μ : Measure X) (g : Y → X → ℝ)
    (hgi : ∀ y, Integrable (g y) μ)
    (φ : X → ℂ) (hφ : Measurable φ) (hb : ∀ x, ‖φ x‖ ≤ 1) :
    law.complexMean (fun y => ∫ x, (g y x : ℂ) * φ x ∂μ) =
      ∫ x, (law.mean (fun y => g y x) : ℂ) * φ x ∂μ := by
  refine (law.complexMean_integral μ _ (fun y =>
    (hgi y).ofReal.mul_bdd hφ.aestronglyMeasurable (Filter.Eventually.of_forall hb))).trans ?_
  exact integral_congr_ae (Filter.Eventually.of_forall (fun x =>
    law.complexMean_ofReal_mul (fun y => g y x) (φ x)))

end FiniteProbabilityWeights
end Erdos3

end

end OAI
