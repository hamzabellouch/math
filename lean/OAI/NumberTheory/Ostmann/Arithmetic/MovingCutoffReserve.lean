import OAI.NumberTheory.Ostmann.Arithmetic.MovingFrequencyBudget

namespace OAI

/-! # The actual Section 7 gaps supply both integer-transfer reserves -/

namespace Ostmann

private theorem moving_sqrt_reserve (m : ℝ) (hm : 64 ≤ m) : Real.sqrt (4 * m) ≤ m / 4 := by
  have hm0 : 0 ≤ m := by linarith
  have hs := Real.sq_sqrt (show 0 ≤ 4 * m by positivity)
  have hp := mul_nonneg hm0 (sub_nonneg.mpr hm)
  nlinarith [Real.sqrt_nonneg (4 * m)]

theorem movingStepGap_succ (BD Bz z m : ℝ) (n : ℕ) :
    spectatorStepGap BD Bz z ((2 : ℝ) ^ (n + 1)) m =
      2 * spectatorStepGap BD Bz z ((2 : ℝ) ^ n) m +
        (4 / 5 : ℝ) * (2 : ℝ) ^ n * Real.log 2 * m := by
  unfold spectatorStepGap
  rw [Real.log_pow, Real.log_pow]
  push_cast
  rw [pow_succ]
  ring

/-- The next pivot gap exceeds the current Fourier exponent by a positive
linear amount, uniformly over all tree levels. -/
theorem movingCutoff_diagonal_reserve (Bs BD Bz z m : ℝ)
    (hBD : Bs + 1 ≤ BD) (hBz : 8 ≤ Bz)
    (hz : 1 ≤ z) (hm : 64 ≤ m) (n : ℕ) :
    (3 / 20 : ℝ) * (2 : ℝ) ^ n * m ≤
      spectatorStepGap BD Bz z ((2 : ℝ) ^ n) m - movingCutoffExponent Bs BD Bz z m n := by
  have hsqrt := moving_sqrt_reserve m hm
  have hm0 : 0 ≤ m := by linarith
  have hlogz := Real.log_nonneg hz
  have hlog2 : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h ⊢
    linarith
  induction n with
  | zero =>
    rw [movingCutoffExponent_zero]
    simp only [spectatorStepGap, spectatorBaseGap, pow_zero, one_mul, Real.log_one,
      mul_zero, add_zero]
    have hb : Bs + 8 * Real.log z + 1 ≤ BD + Bz * Real.log z := by
      nlinarith [mul_nonneg (show 0 ≤ Bz - 8 by linarith) hlogz]
    nlinarith [mul_le_mul_of_nonneg_right hb hm0]
  | succ n ih =>
    rw [movingStepGap_succ, movingCutoffExponent_succ, pow_succ]
    have hr : 0 ≤ (2 : ℝ) ^ n := by positivity
    have hsl := mul_le_mul_of_nonneg_left hsqrt hr
    have hl := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hlog2 hr) hm0
    nlinarith

/-- The frequency range at the next level has a square-root reserve after
paying both the previous frequency and the current pivot gap. -/
theorem movingCutoff_frequency_reserve (Bs BD Bz z m : ℝ) (n : ℕ) :
    movingCutoffExponent Bs BD Bz z m (n + 1) -
      (movingCutoffExponent Bs BD Bz z m n +
        spectatorStepGap BD Bz z ((2 : ℝ) ^ n) m) =
      (2 : ℝ) ^ n * Real.sqrt (4 * m) := by
  rw [movingCutoffExponent_succ]
  ring

end Ostmann

end OAI
