import OAI.MeasureTheory.Falconer.Radial.RadialFreezing

namespace OAI

/-! # A hit child lies in a slightly enlarged radial collision ball -/

namespace Falconer
open NormedSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem radial_cap_child_distance (x z q y u : E) {r D s : ℝ}
    (hs : 0 < s) (hyx : s ≤ ‖y-x‖) (hzx : z ≠ x)
    (hzcap : ‖normalize (z-x)-u‖ ≤ r) (hqcap : ‖normalize (q-x)-u‖ ≤ r)
    (hyz : ‖y-z‖ ≤ D) :
    dist (normalize (y-x)) (normalize (q-x)) ≤ 2*D/s+2*r := by
  have hnear : dist (normalize (y-x)) (normalize (z-x)) ≤ 2*D/s := by
    apply (le_div_iff₀ hs).mpr
    have hh := normalize_distance_scaled hyx (sub_ne_zero.mpr hzx)
    simp only [dist_eq_norm,sub_sub_sub_cancel_right] at hh ⊢
    nlinarith
  have hcap : dist (normalize (z-x)) (normalize (q-x)) ≤ 2*r := by
    rw [dist_eq_norm]
    have hh := norm_sub_le_norm_sub_add_norm_sub (normalize (z-x)) u (normalize (q-x))
    rw [norm_sub_rev u] at hh
    linarith
  exact (dist_triangle _ _ _).trans (add_le_add hnear hcap)

end Falconer

end OAI
