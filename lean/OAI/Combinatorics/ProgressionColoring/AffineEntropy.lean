import OAI.Combinatorics.ProgressionColoring.Parameters

namespace OAI

noncomputable section

namespace QuantitativeVanDerWaerden.Parameters

/-- The additive terms in the finite affine count fit in a factor of three. -/
theorem affine_count_factor_le {k D q : ℝ}
    (hk : 1 ≤ k) (hD : 1 ≤ D) (hq : 1 ≤ q) :
    k * (D * q ^ 2 + 1) + 1 ≤ 3 * k * D * q ^ 2 := by
  have hq2 : 1 ≤ q ^ 2 := by nlinarith
  have hDq : 1 ≤ D * q ^ 2 := one_le_mul_of_one_le_of_one_le hD hq2
  have hprod : k ≤ k * (D * q ^ 2) :=
    le_mul_of_one_le_right (by linarith) hDq
  have hprod1 : 1 ≤ k * (D * q ^ 2) := hk.trans hprod
  nlinarith

/-- A convenient multiplicative form of the actual finite count bound. -/
theorem affine_count_le_simple {k D q Tglob Taff : ℝ}
    (hk : 1 ≤ k) (hD : 1 ≤ D) (hq : 1 ≤ q)
    (hTglob : 0 ≤ Tglob)
    (hcount : Taff ≤ 25 * Tglob * (k * (D * q ^ 2 + 1) + 1) ^ 8) :
    Taff ≤ 25 * Tglob * (3 * k * D * q ^ 2) ^ 8 := by
  apply hcount.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply pow_le_pow_left₀ _ (affine_count_factor_le hk hD hq) 8
  positivity

/-- The rounded dimension contributes at most twice the logarithm of `k`. -/
theorem log_dimension_le_two_log {k : ℕ} (hk : 2 ≤ k) :
    Real.log (dimension k : ℝ) ≤ 2 * Real.log (k : ℝ) := by
  have hk1 : 1 ≤ k := le_trans (by norm_num : 1 ≤ 2) hk
  have hk2 : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (0 : ℝ) < k := by linarith
  have hD0 : (0 : ℝ) < dimension k := by exact_mod_cast dimension_pos hk1
  have hlogk : 0 ≤ Real.log (k : ℝ) := Real.log_natCast_nonneg k
  have hlogtwo : Real.log (2 : ℝ) ≤ Real.log (k : ℝ) :=
    Real.log_le_log (by norm_num) hk2
  have hbound := Real.log_le_log hD0 (dimension_upper hk1)
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0)
      (ne_of_gt (Real.rpow_pos_of_pos hk0 _)), Real.log_rpow hk0] at hbound
  linarith

/-- The finite affine count has entropy of order `k^(9/10) log k`, with a
constant independent of the number of colors. -/
theorem affine_entropy_bound {k : ℕ} (hk : 32 ≤ k)
    {Taff Tglob q A : ℝ}
    (hTaff : 1 ≤ Taff) (hTglob : 1 ≤ Tglob) (hq : 1 ≤ q) (hA : 0 ≤ A)
    (hcount : Taff ≤ 25 * Tglob *
      ((k : ℝ) * ((dimension k : ℝ) * q ^ 2 + 1) + 1) ^ 8)
    (hglobal : Real.log Tglob ≤
      A * (k : ℝ) ^ (3 / 10 : ℝ) * Real.log (k : ℝ))
    (hprime : Real.log q ≤
      4 * (k : ℝ) ^ (9 / 10 : ℝ) * Real.log (k : ℝ)) :
    Real.log Taff ≤ (A + 108) * (k : ℝ) ^ (9 / 10 : ℝ) * Real.log (k : ℝ) := by
  have hk1 : 1 ≤ k := le_trans (by norm_num : 1 ≤ 32) hk
  have hk2 : 2 ≤ k := le_trans (by norm_num : 2 ≤ 32) hk
  have hk32 : (32 : ℝ) ≤ k := by exact_mod_cast hk
  have hk1r : (1 : ℝ) ≤ k := by exact_mod_cast hk1
  have hk0 : (0 : ℝ) < k := by linarith
  have hD1 : (1 : ℝ) ≤ dimension k := by
    exact_mod_cast Nat.succ_le_of_lt (dimension_pos hk1)
  have hD0 : (0 : ℝ) < dimension k := by linarith
  have hq0 : 0 < q := by linarith
  have hg0 : 0 < Tglob := by linarith
  have ha0 : 0 < Taff := by linarith
  have hlogk : 0 ≤ Real.log (k : ℝ) := Real.log_natCast_nonneg k
  have hlogD := log_dimension_le_two_log hk2
  have hlog25 : Real.log (25 : ℝ) ≤ Real.log (k : ℝ) :=
    Real.log_le_log (by norm_num) (by linarith)
  have hlog3 : Real.log (3 : ℝ) ≤ Real.log (k : ℝ) :=
    Real.log_le_log (by norm_num) (by linarith)
  have hsimple := affine_count_le_simple hk1r hD1 hq hg0.le hcount
  have hlogbase :
      Real.log (3 * (k : ℝ) * (dimension k : ℝ) * q ^ 2) =
        Real.log 3 + Real.log (k : ℝ) + Real.log (dimension k : ℝ) +
          2 * Real.log q := by
    rw [Real.log_mul (by positivity) (pow_ne_zero 2 hq0.ne'),
      Real.log_mul (by positivity) hD0.ne',
      Real.log_mul (by norm_num) hk0.ne', Real.log_pow]
    norm_num
  have hlogcount : Real.log Taff ≤ Real.log 25 + Real.log Tglob +
      8 * (Real.log 3 + Real.log (k : ℝ) + Real.log (dimension k : ℝ) +
        2 * Real.log q) := by
    have hb := Real.log_le_log ha0 hsimple
    rw [Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by norm_num) hg0.ne', Real.log_pow, hlogbase] at hb
    norm_num at hb ⊢
    exact hb
  have hfinite : Real.log Taff ≤ Real.log Tglob +
      33 * Real.log (k : ℝ) + 16 * Real.log q := by
    linarith only [hlogcount, hlog25, hlog3, hlogD]
  have hsmall : (k : ℝ) ^ (3 / 10 : ℝ) ≤ (k : ℝ) ^ (9 / 10 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hk1r (by norm_num)
  have hglobal' : Real.log Tglob ≤
      A * (k : ℝ) ^ (9 / 10 : ℝ) * Real.log (k : ℝ) :=
    hglobal.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hsmall hA) hlogk)
  have hscale : Real.log (k : ℝ) ≤
      (k : ℝ) ^ (9 / 10 : ℝ) * Real.log (k : ℝ) :=
    le_mul_of_one_le_left hlogk (Real.one_le_rpow hk1r (by norm_num))
  have hscale0 : 0 ≤ (k : ℝ) ^ (9 / 10 : ℝ) * Real.log (k : ℝ) :=
    mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg k) _) hlogk
  nlinarith only [hfinite, hglobal', hprime, hscale, hscale0]

end QuantitativeVanDerWaerden.Parameters

end

end OAI
