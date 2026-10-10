import OAI.NumberTheory.TwoPointCorrelations.HalaszDistanceCutoff

namespace OAI

/-! The elementary losses when changing the prime cutoff by a fixed power. -/

namespace TwoPointCorrelations

lemma halasz_decay_shift {M K : ℝ} (hM : 0 ≤ M) (hK : 0 ≤ K) :
    (max 0 (M - K) + 1) * Real.exp (-max 0 (M - K)) ≤
      Real.exp K * ((M + 1) * Real.exp (-M)) := by
  by_cases hMK : M ≤ K
  · rw [max_eq_left (by linarith : M - K ≤ 0)]
    simp only [zero_add, neg_zero, Real.exp_zero, mul_one]
    have he : 1 ≤ Real.exp K * Real.exp (-M) := by
      rw [← Real.exp_add]
      exact Real.one_le_exp_iff.mpr (by linarith)
    have hmul := mul_le_mul_of_nonneg_right (show 1 ≤ M + 1 by linarith)
      (mul_nonneg (Real.exp_nonneg K) (Real.exp_nonneg (-M)))
    nlinarith
  · rw [max_eq_right (by linarith : 0 ≤ M - K)]
    have he : Real.exp (-(M - K)) = Real.exp K * Real.exp (-M) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [he]
    have hh := mul_le_mul_of_nonneg_right (show M - K + 1 ≤ M + 1 by linarith)
      (mul_nonneg (Real.exp_nonneg K) (Real.exp_nonneg (-M)))
    nlinarith

lemma halasz_log_error_cutoff {n N : ℕ} (hn : 2 ≤ n) (hnN : n ≤ N)
    (hNc : N ≤ n ^ 3) (hllN : 0 ≤ Real.log (Real.log (N : ℝ))) :
    Real.log (Real.log (n : ℝ)) / Real.log n ≤
      3 * (Real.log (Real.log (N : ℝ)) / Real.log N) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hln : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
  have hlN : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < N))
  have hlnN : Real.log (n : ℝ) ≤ Real.log (N : ℝ) :=
    Real.log_le_log hn0 (by exact_mod_cast hnN)
  have hln3 : Real.log (N : ℝ) ≤ 3 * Real.log (n : ℝ) := by
    have h := Real.log_le_log hN0 (show (N : ℝ) ≤ (n : ℝ) ^ 3 by exact_mod_cast hNc)
    simpa only [Real.log_pow, Nat.cast_ofNat] using h
  calc
    _ ≤ Real.log (Real.log (N : ℝ)) / Real.log n :=
      div_le_div_of_nonneg_right (Real.log_le_log hln hlnN) hln.le
    _ ≤ 3 * (Real.log (Real.log (N : ℝ)) / Real.log N) := by
      rw [← mul_div_assoc]
      apply (div_le_div_iff₀ hln hlN).mpr
      nlinarith [mul_le_mul_of_nonneg_left hln3 hllN]

end TwoPointCorrelations

end OAI
