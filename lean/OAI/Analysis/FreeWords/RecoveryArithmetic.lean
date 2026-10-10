import Mathlib

namespace OAI

noncomputable section

namespace KKFreeWords

theorem recovery_moment_arithmetic {n N m2 m4 b2 b4 s : ℝ}
    (hn : 0 < n) (hN : 100*n ≤ N) (henergy : 2*N/3 ≤ m2)
    (hfourth : m4 ≤ N^2*m2) (hb2 : n*b2 = m2)
    (hb4 : n^3*b4 = m4+2*(n-1)*m2^2)
    (hs0 : 0 ≤ s) (hinterp : b2^3 ≤ s^2*b4) : 3/5 ≤ s := by
  have hN0 : 0 ≤ N := by linarith
  have hm2 : 0 < m2 := by linarith
  have hn2 : 8*n ≤ m2 := by linarith
  have hNN : N ≤ 3/2*m2 := by linarith
  have hNN2 := pow_le_pow_left₀ hN0 hNN 2
  have hNm := mul_le_mul_of_nonneg_right hNN2 hm2.le
  have hnm := mul_le_mul_of_nonneg_right hn2 (sq_nonneg m2)
  have hD : n^3*b4 ≤ 5/2*m2^3 := by nlinarith [sq_nonneg m2]
  have hI : m2^3 ≤ s^2*(n^3*b4) := by
    calc m2^3 = (n*b2)^3 := by rw [hb2]
      _ = n^3*b2^3 := mul_pow n b2 3
      _ ≤ n^3*(s^2*b4) := mul_le_mul_of_nonneg_left hinterp (by positivity)
      _ = _ := by ring
  have hI' := hI.trans (mul_le_mul_of_nonneg_left hD (sq_nonneg s))
  have he : m2^3*1 ≤ m2^3*(5/2*s^2) := by nlinarith [hI']
  have hs := (mul_le_mul_iff_right₀ (pow_pos hm2 3)).mp he
  nlinarith

end KKFreeWords
end

end OAI
