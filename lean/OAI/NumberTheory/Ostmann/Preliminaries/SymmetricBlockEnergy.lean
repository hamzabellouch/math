import Mathlib.Tactic

namespace OAI

/-! # The numerical two-block estimate used in Lemma 5.2 -/

namespace Ostmann

/-- A gap of `1/20` in the second diagonal block means that off-diagonal
size `r` costs only `20*r^2` in the operator bound. -/
theorem symmetric_block_energy (s d r x y : ℝ) (hs : 0 ≤ s) (hd : 0 ≤ d)
    (hgap : d + 1 / 20 ≤ s) :
    (s * x + r * y) ^ 2 + (r * x + d * y) ^ 2 ≤
      (s + 20 * r ^ 2) ^ 2 * (x ^ 2 + y ^ 2) := by
  let M := s + 20 * r ^ 2
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hrow1 : (s * x + r * y) ^ 2 ≤ M * (s * x ^ 2 + y ^ 2 / 20) := by
    have he : M * (s * x ^ 2 + y ^ 2 / 20) - (s * x + r * y) ^ 2 =
        s / 20 * (20 * r * x - y) ^ 2 := by dsimp [M]; ring
    have hn : 0 ≤ s / 20 * (20 * r * x - y) ^ 2 := mul_nonneg (by positivity) (sq_nonneg _)
    linarith
  have hrow2 : (r * x + d * y) ^ 2 ≤
      (d + 1 / 20) * (20 * r ^ 2 * x ^ 2 + d * y ^ 2) := by
    have he : (d + 1 / 20) * (20 * r ^ 2 * x ^ 2 + d * y ^ 2) -
        (r * x + d * y) ^ 2 = d / 20 * (20 * r * x - y) ^ 2 := by ring
    have hn : 0 ≤ d / 20 * (20 * r * x - y) ^ 2 := mul_nonneg (by positivity) (sq_nonneg _)
    linarith
  have hrow2' : (r * x + d * y) ^ 2 ≤ M * (20 * r ^ 2 * x ^ 2 + d * y ^ 2) :=
    hrow2.trans (mul_le_mul_of_nonneg_right (by change d + 1 / 20 ≤ s + 20 * r ^ 2; nlinarith [sq_nonneg r])
      (by positivity))
  have hfinal : M * (s * x ^ 2 + y ^ 2 / 20) +
      M * (20 * r ^ 2 * x ^ 2 + d * y ^ 2) ≤ M ^ 2 * (x ^ 2 + y ^ 2) := by
    have hy := mul_le_mul_of_nonneg_right (hgap.trans (by change s ≤ s + 20 * r ^ 2; nlinarith [sq_nonneg r]))
      (sq_nonneg y)
    have hh := mul_le_mul_of_nonneg_left hy hM
    dsimp [M] at *
    nlinarith only [hh]
  exact (add_le_add hrow1 hrow2').trans hfinal

end Ostmann

end OAI
