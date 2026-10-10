import OAI.Geometry.EinsteinFour.RadialIntegrals

namespace OAI

/-! The exact integral of the refined lower-volume comparison kernel. -/
namespace PositiveEinsteinFour.VolumeConstants
open MeasureTheory
noncomputable section

def lowerVolumeKernel (u : ℝ) : ℝ :=
  (2 * Real.pi ^ 3 / 9) * u ^ 2 * Real.sin (Real.pi * u) + lowerKernel u

theorem integral_square_sine :
    (∫ u in (0 : ℝ)..1, u ^ 2 * Real.sin (Real.pi * u)) =
      (Real.pi ^ 2 - 4) / Real.pi ^ 3 := by
  let F := fun u : ℝ => -u ^ 2 * Real.cos (Real.pi * u) / Real.pi +
    2 * u * Real.sin (Real.pi * u) / Real.pi ^ 2 +
    2 * Real.cos (Real.pi * u) / Real.pi ^ 3
  have hd (u : ℝ) : HasDerivAt F (u ^ 2 * Real.sin (Real.pi * u)) u := by
    have hs := (Real.hasDerivAt_sin (Real.pi * u)).comp u ((hasDerivAt_id u).const_mul Real.pi)
    have hc := (Real.hasDerivAt_cos (Real.pi * u)).comp u ((hasDerivAt_id u).const_mul Real.pi)
    convert (((((hasDerivAt_id u).pow 2).neg.mul hc).div_const Real.pi).add
      (((((hasDerivAt_id u).const_mul 2).mul hs).div_const (Real.pi ^ 2)))).add
      ((hc.const_mul 2).div_const (Real.pi ^ 3)) using 1
    · rfl
    · simp only [Function.comp_apply, Pi.neg_apply, Pi.pow_apply, id_eq]
      field_simp [Real.pi_ne_zero]
      ring
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hd u)
    ((by fun_prop : Continuous (fun u : ℝ => u ^ 2 * Real.sin (Real.pi * u))).intervalIntegrable 0 1)
  rw [h]
  dsimp [F]
  simp only [one_pow, mul_one, Real.cos_pi, Real.sin_pi, mul_zero, zero_mul, Real.cos_zero,
    zero_pow (by decide : 2 ≠ 0), zero_div]
  field_simp
  ring

theorem integral_lowerVolumeKernel :
    (∫ u in (0 : ℝ)..1, lowerVolumeKernel u) =
      2 * (Real.pi ^ 2 - 4) / 9 + ∫ u in (0 : ℝ)..1, lowerKernel u := by
  have h1 : IntervalIntegrable (fun u : ℝ => (2 * Real.pi ^ 3 / 9) * u ^ 2 *
      Real.sin (Real.pi * u)) volume 0 1 := (by fun_prop : Continuous _).intervalIntegrable _ _
  have h2 : IntervalIntegrable lowerKernel volume 0 1 :=
    (by unfold lowerKernel; fun_prop : Continuous _).intervalIntegrable _ _
  change (∫ u in (0 : ℝ)..1, ((2 * Real.pi ^ 3 / 9) * u ^ 2 * Real.sin (Real.pi * u) +
    lowerKernel u)) = _
  rw [intervalIntegral.integral_add h1 h2]
  congr 1
  simp_rw [mul_assoc]
  rw [intervalIntegral.integral_const_mul, integral_square_sine]
  field_simp

theorem integral_lowerVolumeKernel_gt :
    (4 / 3 : ℝ) < ∫ u in (0 : ℝ)..1, lowerVolumeKernel u := by
  rw [integral_lowerVolumeKernel]
  exact analytic_lower_margin

end
end PositiveEinsteinFour.VolumeConstants

end OAI
