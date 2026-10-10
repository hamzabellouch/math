import Mathlib.Tactic
import Mathlib.Topology.MetricSpace.Basic

namespace OAI

/-! # Weighted squared distance is minimal at a geodesic interpolation point -/

namespace RegularPointCoordinates
variable {X : Type*} [PseudoMetricSpace X]

theorem weighted_sq_dist_lower (x y z : X) {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    θ*(1-θ)*dist x y^2 ≤ (1-θ)*dist z x^2+θ*dist z y^2 := by
  have hd : dist x y ≤ dist z x+dist z y := by simpa only [dist_comm x z] using dist_triangle x z y
  have hs := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ dist_nonneg hd 2)
    (mul_nonneg hθ0 (sub_nonneg.mpr hθ1))
  nlinarith [sq_nonneg ((1-θ)*dist z x-θ*dist z y)]

theorem weighted_sq_dist_at_geodesic (x y z : X) {θ : ℝ}
    (hx : dist z x=θ*dist x y) (hy : dist z y=(1-θ)*dist x y) :
    (1-θ)*dist z x^2+θ*dist z y^2=θ*(1-θ)*dist x y^2 := by
  rw [hx,hy]
  ring

end RegularPointCoordinates

end OAI
