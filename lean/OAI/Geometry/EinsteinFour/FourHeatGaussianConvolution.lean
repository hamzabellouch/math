import OAI.Geometry.EinsteinFour.FourHeatGaussian

namespace OAI

/-! Completing the square gives the exact Euclidean heat semigroup. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory

noncomputable section

theorem fourHeatGaussian_complete_square (t s : ℝ) (ht : 0 < t) (hs : 0 < s)
    (x y : FourSpace) :
    -(4 * t)⁻¹ * ‖x - y‖ ^ 2 + -(4 * s)⁻¹ * ‖y‖ ^ 2 =
      -(4 * (t + s))⁻¹ * ‖x‖ ^ 2 +
      -(4 * (t * s / (t + s)))⁻¹ * ‖y - (s / (t + s)) • x‖ ^ 2 := by
  have hts : t + s ≠ 0 := ne_of_gt (add_pos ht hs)
  rw [norm_sub_sq_real, norm_sub_sq_real, inner_smul_right, norm_smul,
    Real.norm_eq_abs, mul_pow, sq_abs, real_inner_comm y x]
  field_simp
  ring

theorem fourHeatGaussian_product (t s : ℝ) (ht : 0 < t) (hs : 0 < s)
    (x y : FourSpace) :
    fourHeatGaussian t (x - y) * fourHeatGaussian s y =
      fourHeatGaussian (t + s) x *
        fourHeatGaussian (t * s / (t + s)) (y - (s / (t + s)) • x) := by
  have hts : t + s ≠ 0 := ne_of_gt (add_pos ht hs)
  have hp : (((4 * Real.pi * t) ^ 2)⁻¹ * ((4 * Real.pi * s) ^ 2)⁻¹) =
      ((4 * Real.pi * (t + s)) ^ 2)⁻¹ *
        ((4 * Real.pi * (t * s / (t + s))) ^ 2)⁻¹ := by
    field_simp [Real.pi_ne_zero]
  unfold fourHeatGaussian
  calc
    _ = (((4 * Real.pi * t) ^ 2)⁻¹ * ((4 * Real.pi * s) ^ 2)⁻¹) *
        Real.exp (-(4 * t)⁻¹ * ‖x - y‖ ^ 2 + -(4 * s)⁻¹ * ‖y‖ ^ 2) := by
      rw [Real.exp_add]
      ring
    _ = _ := by
      rw [hp, fourHeatGaussian_complete_square t s ht hs x y, Real.exp_add]
      ring

theorem fourHeatGaussian_convolution (t s : ℝ) (ht : 0 < t) (hs : 0 < s)
    (x : FourSpace) :
    (∫ y : FourSpace, fourHeatGaussian t (x - y) * fourHeatGaussian s y) =
      fourHeatGaussian (t + s) x := by
  simp_rw [fourHeatGaussian_product t s ht hs x]
  rw [integral_const_mul, integral_sub_right_eq_self,
    fourHeatGaussian_mass (t * s / (t + s)) (div_pos (mul_pos ht hs) (add_pos ht hs)),
    mul_one]

theorem fourHeatGaussian_product_integrable (t s : ℝ) (ht : 0 < t) (hs : 0 < s)
    (x : FourSpace) :
    Integrable (fun y : FourSpace => fourHeatGaussian t (x - y) * fourHeatGaussian s y) := by
  simp_rw [fourHeatGaussian_product t s ht hs x]
  exact ((fourHeatGaussian_integrable (t * s / (t + s))
    (div_pos (mul_pos ht hs) (add_pos ht hs))).comp_sub_right _).const_mul _

end
end PositiveEinsteinFour.Geometry

end OAI
