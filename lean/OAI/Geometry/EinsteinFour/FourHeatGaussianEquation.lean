import OAI.Geometry.EinsteinFour.FourHeatGaussianDifferential

namespace OAI

/-! The normalized Gaussian solves the actual flat heat equation. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour
open scoped BigOperators

noncomputable section

theorem fourHeatGaussian_hasDerivAt_time (t : ℝ) (ht : 0 < t) (x : FourSpace) :
    HasDerivAt (fun s => fourHeatGaussian s x)
      ((‖x‖ ^ 2 / (4 * t ^ 2) - 2 / t) * fourHeatGaussian t x) t := by
  have ht4 : 4 * t ≠ 0 := mul_ne_zero (by norm_num) ht.ne'
  have hp : 4 * Real.pi * t ≠ 0 := by positivity
  have ha := (((hasDerivAt_id t).const_mul (4 * Real.pi)).pow 2).inv (pow_ne_zero 2 hp)
  have hb := (((((hasDerivAt_id t).const_mul 4).inv ht4).neg).mul_const (‖x‖ ^ 2)).exp
  have hh := ha.mul hb
  convert hh using 1
  · rfl
  · simp only [fourHeatGaussian, id_eq, Pi.inv_apply, Pi.pow_apply, Pi.neg_apply, mul_one]
    field_simp
    ring

theorem fourHeatGaussian_heat_equation (t : ℝ) (ht : 0 < t) (x : FourSpace) :
    HasDerivAt (fun s => fourHeatGaussian s x)
      (∑ i : Fin 4, partialDeriv (partialDeriv (fourHeatGaussian t) i) i x) t := by
  rw [fourHeatGaussian_spatial_laplacian t ht.ne']
  exact fourHeatGaussian_hasDerivAt_time t ht x

end
end PositiveEinsteinFour.Geometry

end OAI
