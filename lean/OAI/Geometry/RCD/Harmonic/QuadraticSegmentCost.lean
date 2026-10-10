import Mathlib.Tactic

namespace OAI

/-! # The sharp quadratic cost bound at an interior segment point -/

namespace RegularPointCoordinates

theorem quadratic_segment_cost {r d l s : ℝ}
    (hl : 0 ≤ l) (hs : 0 < s) (hs1 : s ≤ 1)
    (htri : l ≤ r+(1-s)*d) :
    l^2-d^2-r^2/s ≤ -s*d^2 := by
  have hsq : l^2 ≤ (r+(1-s)*d)^2 := by
    nlinarith
  have hpos : 0 ≤ (1-s)*(r-s*d)^2/s :=
    div_nonneg (mul_nonneg (sub_nonneg.mpr hs1) (sq_nonneg _)) hs.le
  have he : (r+(1-s)*d)^2-d^2-r^2/s+s*d^2 = -(1-s)*(r-s*d)^2/s := by
    field_simp
    ring
  simp only [neg_mul,neg_div] at he
  linarith

end RegularPointCoordinates

end OAI
