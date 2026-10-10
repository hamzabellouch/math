import OAI.Geometry.RCD.Heat.BoundedExponentialIntegral

namespace OAI

/-! # Strict positivity of bounded exponential tilts

The lower bound retains the mass of the original integrable weight.
It applies to the compact-support positive kernel rows without a
pointwise positive lower bound on the endpoint density.
-/

open Set Filter MeasureTheory
open scoped NNReal
noncomputable section
namespace RegularPointCoordinates
variable {Y : Type*} [MeasurableSpace Y] (μ : Measure Y)

theorem exponential_tilt_mass_lower {r g : Y → ℝ} (hr : Integrable r μ)
    (hr0 : ∀ᵐ x ∂μ, 0 ≤ r x) (hg : Measurable g)
    {M : ℝ≥0} (hgb : ∀ x, |g x| ≤ M) (t : ℝ) :
    Real.exp (- (|t| * M)) * (∫ x, r x ∂μ) ≤
      ∫ x, Real.exp (t*g x)*r x ∂μ := by
  rw [← integral_const_mul]
  apply integral_mono_ae (hr.const_mul _) (bounded_exp_mul_integrable μ hr hg hgb t)
  filter_upwards [hr0] with x hx
  apply mul_le_mul_of_nonneg_right _ hx
  apply Real.exp_le_exp.mpr
  have hb : |t*g x| ≤ |t| * M := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hgb x) (abs_nonneg t)
  exact (neg_le_neg hb).trans (neg_abs_le _)

theorem exponential_tilt_mass_pos {r g : Y → ℝ} (hr : Integrable r μ)
    (hr0 : ∀ᵐ x ∂μ, 0 ≤ r x) (hmass : 0 < ∫ x, r x ∂μ)
    (hg : Measurable g) {M : ℝ≥0} (hgb : ∀ x, |g x| ≤ M) (t : ℝ) :
    0 < ∫ x, Real.exp (t*g x)*r x ∂μ :=
  (mul_pos (Real.exp_pos _) hmass).trans_le
    (exponential_tilt_mass_lower μ hr hr0 hg hgb t)

end RegularPointCoordinates

end

end OAI
