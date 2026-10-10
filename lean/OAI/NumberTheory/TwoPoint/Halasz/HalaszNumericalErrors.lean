import OAI.NumberTheory.TwoPoint.Halasz.HalaszParameters

namespace OAI

/-! The logarithmic height and integer smoothing length absorb the two
errors in the grouped Perron estimate. -/

namespace TwoPointCorrelations

lemma halasz_numerical_errors {N m : ℕ} {C H : ℝ}
    (hN : 3 ≤ N) (hC : 0 ≤ C) (hH : 0 ≤ H)
    (hlog : 1 ≤ Real.log (N : ℝ)) (hm : 0 < m)
    (hml : (m : ℝ) ≤ 2 * ((N : ℝ) / Real.log (N : ℝ) ^ 4))
    (hmu : ((N : ℝ) + 1 / 2) / m ≤ 2 * Real.log (N : ℝ) ^ 4) :
    C * N * (H * Real.log N) * Real.log N /
        (((m : ℝ) / ((N : ℝ) + 1 / 2)) * Real.log N ^ 8) +
      C * m * Real.log (3 * N) ^ 2 ≤ (2 * C * H + 8 * C) * N := by
  let ℓ := Real.log (N : ℝ)
  have hℓ : 1 ≤ ℓ := hlog
  have hℓ0 : 0 < ℓ := by linarith
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hfac : ℓ ^ 2 * (((N : ℝ) + 1 / 2) / m) ≤ 2 * ℓ ^ 8 := by
    calc
      _ ≤ ℓ ^ 2 * (2 * ℓ ^ 4) := mul_le_mul_of_nonneg_left hmu (sq_nonneg _)
      _ = 2 * ℓ ^ 6 := by ring
      _ ≤ 2 * ℓ ^ 8 := mul_le_mul_of_nonneg_left
        (pow_le_pow_right₀ hℓ (by norm_num : (6 : ℕ) ≤ 8)) (by norm_num)
  have hfacdiv : ℓ ^ 2 * (((N : ℝ) + 1 / 2) / m) / ℓ ^ 8 ≤ 2 :=
    (div_le_iff₀ (pow_pos hℓ0 8)).mpr hfac
  have htail : C * N * (H * ℓ) * ℓ /
      (((m : ℝ) / ((N : ℝ) + 1 / 2)) * ℓ ^ 8) ≤ 2 * C * H * N := by
    calc
      _ = (C * N * H) * (ℓ ^ 2 * (((N : ℝ) + 1 / 2) / m) / ℓ ^ 8) := by
        field_simp
      _ ≤ (C * N * H) * 2 := mul_le_mul_of_nonneg_left hfacdiv (by positivity)
      _ = _ := by ring
  have hlog3 : 0 ≤ Real.log (3 * (N : ℝ)) := by
    apply Real.log_nonneg
    have : (3 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  have hlog3u : Real.log (3 * (N : ℝ)) ≤ 2 * ℓ := by
    rw [Real.log_mul (by norm_num) hN0.ne']
    have : Real.log 3 ≤ ℓ := Real.log_le_log (by norm_num) (by exact_mod_cast hN)
    linarith
  have hboundary : C * m * Real.log (3 * (N : ℝ)) ^ 2 ≤ 8 * C * N := by
    calc
      _ ≤ C * (2 * ((N : ℝ) / ℓ ^ 4)) * (2 * ℓ) ^ 2 := by gcongr
      _ = 8 * C * N / ℓ ^ 2 := by field_simp; ring
      _ ≤ 8 * C * N := div_le_self (by positivity) (one_le_pow₀ hℓ)
  change C * N * (H * ℓ) * ℓ /
      (((m : ℝ) / ((N : ℝ) + 1 / 2)) * ℓ ^ 8) +
      C * m * Real.log (3 * (N : ℝ)) ^ 2 ≤ _
  linarith

end TwoPointCorrelations

end OAI
