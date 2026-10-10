import OAI.Geometry.SurfaceImmersion.Whitney.CollarVelocity

namespace OAI

/-! Exact mean constraints for the explicit collar velocity arc. -/
noncomputable section
open MeasureTheory

namespace ClosedSurfaceR4.CollarVelocity

def circleMean (f : ℝ → ℝ) : ℝ := (2 * Real.pi)⁻¹ * ∫ t in 0..2 * Real.pi, f t

lemma integral_cos_period : (∫ t in (0 : ℝ)..2 * Real.pi, Real.cos t) = 0 := by
  rw [integral_cos]
  simp

lemma integral_cos_sq_period : (∫ t in (0 : ℝ)..2 * Real.pi, Real.cos t ^ 2) = Real.pi := by
  rw [integral_cos_sq]
  simp

lemma integral_arc_den (a : ℝ) :
    (∫ t in (0 : ℝ)..2 * Real.pi, 1 + (a * Real.cos t) ^ 2) =
      2 * Real.pi * (1 + a ^ 2 / 2) := by
  simp only [mul_pow]
  rw [intervalIntegral.integral_add (f := fun _ : ℝ => (1 : ℝ))
    (g := fun t : ℝ => a ^ 2 * Real.cos t ^ 2) intervalIntegrable_const
    ((continuous_const.mul (Real.continuous_cos.pow 2)).intervalIntegrable _ _),
    intervalIntegral.integral_const, intervalIntegral.integral_const_mul,
    integral_cos_sq_period]
  simp only [sub_zero, smul_eq_mul, mul_one]
  ring

lemma integral_arc_num (a : ℝ) :
    (∫ t in (0 : ℝ)..2 * Real.pi, 1 - (a * Real.cos t) ^ 2) =
      2 * Real.pi * (1 - a ^ 2 / 2) := by
  simp only [mul_pow]
  rw [intervalIntegral.integral_sub (f := fun _ : ℝ => (1 : ℝ))
    (g := fun t : ℝ => a ^ 2 * Real.cos t ^ 2) intervalIntegrable_const
    ((continuous_const.mul (Real.continuous_cos.pow 2)).intervalIntegrable _ _),
    intervalIntegral.integral_const, intervalIntegral.integral_const_mul,
    integral_cos_sq_period]
  simp only [sub_zero, smul_eq_mul, mul_one]
  ring

lemma mean_density (a : ℝ) : circleMean (density a) = 1 := by
  unfold circleMean density
  rw [intervalIntegral.integral_div, integral_arc_den]
  field_simp [(densityDen_pos a).ne', Real.pi_ne_zero]

lemma mean_density_arcX (a : ℝ) :
    circleMean (fun t => density a t * arcX a t) = (1 - a ^ 2 / 2) / (1 + a ^ 2 / 2) := by
  unfold circleMean
  simp_rw [density_mul_arcX]
  rw [intervalIntegral.integral_div, integral_arc_num]
  field_simp [(densityDen_pos a).ne', Real.pi_ne_zero]

lemma mean_density_arcY (a : ℝ) : circleMean (fun t => density a t * arcY a t) = 0 := by
  unfold circleMean
  simp_rw [density_mul_arcY]
  rw [intervalIntegral.integral_div, intervalIntegral.integral_const_mul, integral_cos_period]
  simp

end ClosedSurfaceR4.CollarVelocity

end

end OAI
