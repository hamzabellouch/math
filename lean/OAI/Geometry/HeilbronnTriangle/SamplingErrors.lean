import Mathlib

namespace OAI


namespace Problem355.SamplingErrors

lemma log_bound_of_polynomial_bound {r N : ℝ} {m : ℕ}
    (hr : 1 ≤ r) (hN1 : 1 ≤ N) (hN : N ≤ r ^ m) :
    0 ≤ Real.log (2 * N) ∧ Real.log (2 * N) ≤ (m + 1 : ℝ) * r := by
  have hr0 : 0 < r := lt_of_lt_of_le (by norm_num) hr
  have hN0 : 0 < N := lt_of_lt_of_le (by norm_num) hN1
  have hlogr : Real.log r ≤ r := Real.log_le_self hr0.le
  have hlog2 : Real.log (2 : ℝ) ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have hlogN : Real.log N ≤ (m : ℝ) * Real.log r := by
    simpa only [Real.log_pow] using Real.log_le_log hN0 hN
  constructor
  · apply Real.log_nonneg
    linarith
  · rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hN0.ne']
    have hm : (m : ℝ) * Real.log r ≤ (m : ℝ) * r :=
      mul_le_mul_of_nonneg_left hlogr (Nat.cast_nonneg m)
    nlinarith

lemma pair_error_le {r H n : ℝ} (hr : 1 ≤ r) (hH : r ≤ H)
    (hn : n ≤ r * H ^ 15) :
    n * H ^ 6 / (H ^ 10) ^ 3 ≤ 1 / r ^ 8 := by
  have hr0 : 0 < r := lt_of_lt_of_le (by norm_num) hr
  have hH0 : 0 < H := hr0.trans_le hH
  calc
    n * H ^ 6 / (H ^ 10) ^ 3 ≤
        (r * H ^ 15) * H ^ 6 / (H ^ 10) ^ 3 := by
      gcongr
    _ = r / H ^ 9 := by field_simp
    _ ≤ r / r ^ 9 := by gcongr
    _ = 1 / r ^ 8 := by field_simp

lemma triple_error_le {r N n τ h B L A : ℝ}
    (hr : 1 ≤ r) (hN : 0 < N) (ht : 0 < τ)
    (hh0 : 0 ≤ h)
    (hn : n ^ 2 * τ ≤ r ^ 2 * N ^ 3)
    (hh : h ≤ 3 * B * τ) (hB : B ≤ r ^ 31)
    (hL : L ^ 2 ≤ A ^ 2 * r ^ 2) :
    n ^ 2 * L ^ 2 * h / (N ^ 3 * r ^ 41) ≤ 3 * A ^ 2 / r ^ 6 := by
  have hr0 : 0 < r := lt_of_lt_of_le (by norm_num) hr
  have hn' : n ^ 2 ≤ r ^ 2 * N ^ 3 / τ := (le_div_iff₀ ht).mpr hn
  calc
    n ^ 2 * L ^ 2 * h / (N ^ 3 * r ^ 41) ≤
        (r ^ 2 * N ^ 3 / τ) * (A ^ 2 * r ^ 2) * (3 * B * τ) /
          (N ^ 3 * r ^ 41) := by
      gcongr
    _ ≤ (r ^ 2 * N ^ 3 / τ) * (A ^ 2 * r ^ 2) * (3 * r ^ 31 * τ) /
          (N ^ 3 * r ^ 41) := by
      gcongr
    _ = 3 * A ^ 2 / r ^ 6 := by field_simp

lemma sample_le_power {r H n τ : ℝ} (hr : 1 ≤ r) (hH : r ≤ H)
    (ht : 1 ≤ τ) (hn : n ^ 2 * τ ≤ r ^ 2 * (H ^ 10) ^ 3) :
    n ≤ r * H ^ 15 := by
  have hr0 : 0 ≤ r := le_trans (by norm_num) hr
  have hH0 : 0 ≤ H := hr0.trans hH
  have hnn : n ^ 2 ≤ n ^ 2 * τ := le_mul_of_one_le_right (sq_nonneg n) ht
  have heq : (r * H ^ 15) ^ 2 = r ^ 2 * (H ^ 10) ^ 3 := by ring
  have hpos : 0 ≤ r * H ^ 15 := by positivity
  nlinarith

lemma triple_error_log_le {r H n τ h B : ℝ} {m : ℕ}
    (hr : 1 ≤ r) (hH : r ≤ H) (ht : 1 ≤ τ) (hh0 : 0 ≤ h)
    (hn : n ^ 2 * τ ≤ r ^ 2 * (H ^ 10) ^ 3)
    (hh : h ≤ 3 * B * τ) (hB : B ≤ r ^ 31)
    (hpoly : H ^ 10 ≤ r ^ m) :
    n ^ 2 * (Real.log (2 * H ^ 10)) ^ 2 * h /
      ((H ^ 10) ^ 3 * r ^ 41) ≤ 3 * (m + 1 : ℝ) ^ 2 / r ^ 6 := by
  have hH1 : 1 ≤ H := hr.trans hH
  have hN1 : 1 ≤ H ^ 10 := one_le_pow₀ hH1
  have hlog := log_bound_of_polynomial_bound hr hN1 hpoly
  apply triple_error_le hr (lt_of_lt_of_le (by norm_num) hN1)
    (lt_of_lt_of_le (by norm_num) ht) hh0 hn hh hB
  simpa only [mul_pow] using (sq_le_sq₀ hlog.1 (by positivity)).mpr hlog.2

lemma errors_small {r A Cpair Ctriple epair etriple : ℝ}
    (hr : 1 ≤ r) (hCp : 0 ≤ Cpair) (hCt : 0 ≤ Ctriple)
    (hp : epair ≤ 1 / r ^ 8) (ht : etriple ≤ 3 * A ^ 2 / r ^ 6)
    (hlarge : 4 * Cpair + 24 * Ctriple * A ^ 2 < r) :
    4 * Cpair * epair + 8 * Ctriple * etriple < 1 := by
  have hr0 : 0 < r := lt_of_lt_of_le (by norm_num) hr
  have hr8 : r ≤ r ^ 8 := by
    simpa only [pow_one] using (pow_le_pow_right₀ hr (by norm_num : 1 ≤ 8))
  have hr6 : r ≤ r ^ 6 := by
    simpa only [pow_one] using (pow_le_pow_right₀ hr (by norm_num : 1 ≤ 6))
  calc
    4 * Cpair * epair + 8 * Ctriple * etriple ≤
        4 * Cpair * (1 / r ^ 8) + 8 * Ctriple * (3 * A ^ 2 / r ^ 6) :=
      add_le_add (mul_le_mul_of_nonneg_left hp (by positivity))
        (mul_le_mul_of_nonneg_left ht (by positivity))
    _ = (4 * Cpair) / r ^ 8 + (24 * Ctriple * A ^ 2) / r ^ 6 := by ring
    _ ≤ (4 * Cpair) / r + (24 * Ctriple * A ^ 2) / r :=
      add_le_add (div_le_div_of_nonneg_left (by positivity) hr0 hr8)
        (div_le_div_of_nonneg_left (by positivity) hr0 hr6)
    _ = (4 * Cpair + 24 * Ctriple * A ^ 2) / r := by ring
    _ < 1 := (div_lt_one hr0).mpr hlarge

theorem relative_error_lt_one {r H n τ h B Cpair Ctriple : ℝ} {m : ℕ}
    (hr : 1 ≤ r) (hH : r ≤ H) (ht : 1 ≤ τ) (hh0 : 0 ≤ h)
    (hn : n ^ 2 * τ ≤ r ^ 2 * (H ^ 10) ^ 3)
    (hh : h ≤ 3 * B * τ) (hB : B ≤ r ^ 31)
    (hpoly : H ^ 10 ≤ r ^ m)
    (hCp : 0 ≤ Cpair) (hCt : 0 ≤ Ctriple)
    (hlarge : 4 * Cpair + 24 * Ctriple * (m + 1 : ℝ) ^ 2 < r) :
    4 * Cpair * (n * H ^ 6 / (H ^ 10) ^ 3) +
      8 * Ctriple * (n ^ 2 * (Real.log (2 * H ^ 10)) ^ 2 * h /
        ((H ^ 10) ^ 3 * r ^ 41)) < 1 := by
  exact errors_small hr hCp hCt
    (pair_error_le hr hH (sample_le_power hr hH ht hn))
    (triple_error_log_le hr hH ht hh0 hn hh hB hpoly) hlarge

end Problem355.SamplingErrors

end OAI
