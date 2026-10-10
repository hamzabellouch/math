import OAI.Probability.InvariantIsing.Magnetic.MagneticContinuationIBP

namespace OAI

/-! Integrable moments and the scaled Gaussian integration-by-parts identity
used to turn the variance differential of a bounded continuation into its
parabolic generator. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped NNReal

namespace InvariantIsing

lemma magnetic_tilted_shift_integrable {F A : ℝ → ℝ}
    (hF : Measurable F) (hG : HasLinearGrowth F) (hA : Measurable A)
    {C : ℝ} (bA : ∀ x, |A x| ≤ C) (r ζ z : ℝ) :
    Integrable (fun u => A (z + r * u))
      ((gaussianReal 0 1).tilted (fun u => ζ * F (z + r * u))) := by
  have he := integrable_exp_of_linearGrowth (gaussianReal 0 1)
    (gaussianReal_exponentialNormMoments 0 1) (hF.comp (by fun_prop))
    ((hG.add_left z).scale_argument r) ζ
  have : IsProbabilityMeasure ((gaussianReal 0 1).tilted
      (fun u => ζ * F (z + r * u))) := MeasureTheory.isProbabilityMeasure_tilted he
  exact Integrable.of_bound (hA.comp (by fun_prop)).aestronglyMeasurable C
    (Filter.Eventually.of_forall fun u => by
      simpa only [Real.norm_eq_abs] using bA (z + r * u))

lemma magnetic_tilted_linear_integrable {F A : ℝ → ℝ}
    (hF : Measurable F) (hG : HasLinearGrowth F) (hA : Measurable A)
    {C : ℝ} (bA : ∀ x, |A x| ≤ C) (r ζ z : ℝ) :
    Integrable (fun u => u * A (z + r * u))
      ((gaussianReal 0 1).tilted (fun u => ζ * F (z + r * u))) := by
  have hshift := hF.comp (show Measurable (fun u : ℝ => z + r * u) by fun_prop)
  have hg := (hG.add_left z).scale_argument r
  have he := integrable_exp_of_linearGrowth (gaussianReal 0 1)
    (gaussianReal_exponentialNormMoments 0 1) hshift hg ζ
  apply (integrable_tilted_iff he _).mpr
  apply field_exp_mul_linear_integrable 1 0 ζ hshift hg
    (measurable_id.mul (hA.comp (by fun_prop)))
  refine ⟨0, C, le_rfl, (abs_nonneg _).trans (bA 0), fun u => ?_⟩
  change |u * A (z + r * u)| ≤ 0 + C * ‖u‖
  rw [abs_mul, Real.norm_eq_abs, zero_add]
  simpa only [mul_comm] using
    mul_le_mul_of_nonneg_left (bA (z + r * u)) (abs_nonneg u)

lemma magnetic_tilted_scaled_test_ibp {F M A B : ℝ → ℝ}
    (hF : Measurable F) (hG : HasLinearGrowth F)
    (hM : Measurable M) (hA : Measurable A) (hB : Measurable B)
    {K C D : ℝ} (bM : ∀ x, |M x| ≤ K) (bA : ∀ x, |A x| ≤ C)
    (bB : ∀ x, |B x| ≤ D) (dF : ∀ x, HasDerivAt F (M x) x)
    (dA : ∀ x, HasDerivAt A (B x) x) {r : ℝ} (hr : r ≠ 0) (ζ z : ℝ) :
    (∫ u, A (z + r * u) * ((1 / (2 * r)) * u)
      ∂(gaussianReal 0 1).tilted (fun u => ζ * F (z + r * u))) =
      (1 / 2 : ℝ) * (∫ u, B (z + r * u)
        ∂(gaussianReal 0 1).tilted (fun u => ζ * F (z + r * u))) +
      ζ / 2 * (∫ u, A (z + r * u) * M (z + r * u)
        ∂(gaussianReal 0 1).tilted (fun u => ζ * F (z + r * u))) := by
  let ν := (gaussianReal 0 1).tilted (fun u => ζ * F (z + r * u))
  have hiB : Integrable (fun u => B (z + r * u)) ν :=
    magnetic_tilted_shift_integrable hF hG hB bB r ζ z
  have hiAM : Integrable (fun u => A (z + r * u) * M (z + r * u)) ν := by
    apply magnetic_tilted_shift_integrable hF hG (hA.mul hM)
      (C := C * K) (r := r) (ζ := ζ) (z := z)
    intro x
    change |A x * M x| ≤ C * K
    rw [abs_mul]
    exact mul_le_mul (bA x) (bM x) (abs_nonneg _) ((abs_nonneg _).trans (bA 0))
  have he : (fun u => A (z + r * u) * ((1 / (2 * r)) * u)) =
      fun u => (1 / (2 * r)) * (u * A (z + r * u)) := by
    funext u
    ring
  rw [he, integral_const_mul]
  rw [magnetic_gaussian_tilted_test_ibp hF hG hM hA hB bM bA bB dF dA r ζ z]
  have he' : (fun u => B (z + r * u) + ζ * A (z + r * u) * M (z + r * u)) =
      fun u => B (z + r * u) + ζ * (A (z + r * u) * M (z + r * u)) := by
    funext u
    ring
  rw [he', integral_add hiB (hiAM.const_mul ζ), integral_const_mul]
  field_simp [hr]
  ring

end InvariantIsing

end

end OAI
