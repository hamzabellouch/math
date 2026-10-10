import Mathlib

namespace OAI

/-! # A fixed quadratic distance bound -/

namespace RegularPointCoordinates

theorem quadratic_radial_growth_bound {a b e R r : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (he : 0 ≤ e) :
    a+b*(R+r)^2+e ≤ (a+2*b*R^2+2*b+e)*(1+r^2) := by
  have hs : (R+r)^2 ≤ 2*R^2+2*r^2 := by nlinarith [sq_nonneg (R-r)]
  have hp := mul_le_mul_of_nonneg_left hs hb
  have hbase : 0 ≤ a+2*b*R^2+e := by positivity
  have hmul := mul_nonneg hbase (sq_nonneg r)
  nlinarith

end RegularPointCoordinates

end OAI
