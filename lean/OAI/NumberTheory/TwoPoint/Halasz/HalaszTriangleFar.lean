import OAI.NumberTheory.TwoPoint.Halasz.HalaszTriangleTail

namespace OAI

/-! The part of the Fourier kernel whose linear frequency stays away
from the logarithmic derivative. -/
namespace TwoPointCorrelations

lemma halasz_log_far_slope (N u v x : ℝ) (hN : 0 < N) (hx : N/2 ≤ x)
    (hfar : 4*|u| ≤ N*|v|) : |v|/2 ≤ |halaszLogSlope u v x| := by
  have hxp : 0 < x := (half_pos hN).trans_le hx
  have hu : |u/x| ≤ 2*|u|/N := by
    rw [abs_div, abs_of_pos hxp]
    calc
      _ ≤ |u|/(N/2) := div_le_div_of_nonneg_left (abs_nonneg u) (half_pos hN) hx
      _ = _ := by ring
  have hv : 2*|u|/N ≤ |v|/2 := (div_le_iff₀ hN).mpr (by nlinarith)
  have hh := abs_add_le (v-u/x) (u/x)
  rw [sub_add_cancel, abs_sub_comm v (u/x)] at hh
  unfold halaszLogSlope
  linarith

theorem halasz_triangle_far (N u v : ℝ) (hN : 0 < N) (hv : v ≠ 0)
    (hfar : 4*|u| ≤ N*|v|) :
    ‖halaszTriangleIntegral N u v‖ ≤ 512/(N*v^2) := by
  have hvp : 0 < |v| := abs_pos.mpr hv
  apply (halasz_triangle_nonstationary N u v (|v|/2) hN (half_pos hvp)
    (fun x hx => halasz_log_far_slope N u v x hN hx.1 hfar)).trans
  have hs : (4*|u|)^2 ≤ (N*|v|)^2 :=
    pow_le_pow_left₀ (by positivity) hfar 2
  have hm := mul_le_mul_of_nonneg_right hfar (mul_nonneg hN.le (abs_nonneg v))
  rw [← sq_abs v, ← sq_abs u]
  field_simp
  nlinarith

end TwoPointCorrelations

end OAI
