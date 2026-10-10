import OAI.Probability.InvariantIsing.Gaussian.GaussianTiltLinearGrowth

namespace OAI

/-! Completing the square under the finite scalar Gaussian law. This is
the shift identity used to control canonical increments uniformly in the
number and size of the cascade steps. -/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace InvariantIsing

lemma gaussianPDFReal_exp_linear {v : ℝ≥0} (hv : v ≠ 0) (t x : ℝ) :
    gaussianPDFReal 0 v x * Real.exp (t * x) =
      Real.exp (t ^ 2 * v / 2) * gaussianPDFReal (t * v) v x := by
  have hvR : (v : ℝ) ≠ 0 := by exact_mod_cast hv
  have he : -(x ^ 2) / (2 * v) + t * x =
      t ^ 2 * v / 2 + -(x - t * v) ^ 2 / (2 * v) := by
    field_simp
    ring
  simp only [gaussianPDFReal, sub_zero]
  rw [mul_assoc, ← Real.exp_add, he, Real.exp_add]
  ring

theorem gaussian_exp_linear_shift (v : ℝ≥0) (t : ℝ) (F : ℝ → ℝ) (hF : Measurable F) :
    (∫ x, Real.exp (t * x) * F x ∂gaussianReal 0 v) =
      Real.exp (t ^ 2 * v / 2) *
        ∫ x, F (x + t * v) ∂gaussianReal 0 v := by
  by_cases hv : v = 0
  · subst v
    simp
  have hshift : (∫ x, F x ∂gaussianReal (t * v) v) =
      ∫ x, F (x + t * v) ∂gaussianReal 0 v := by
    have he := integral_map (μ := gaussianReal 0 v)
      (f := F) (by fun_prop : AEMeasurable (fun x : ℝ => x + t * v)
        (gaussianReal 0 v)) hF.aestronglyMeasurable
    simpa only [gaussianReal_map_add_const, zero_add] using he
  rw [← hshift, integral_gaussianReal_eq_integral_smul hv,
    integral_gaussianReal_eq_integral_smul hv, ← integral_const_mul]
  apply integral_congr_ae
  apply ae_of_all
  intro x
  simp only [smul_eq_mul]
  rw [← mul_assoc, gaussianPDFReal_exp_linear hv]
  ring

end InvariantIsing

end

end OAI
