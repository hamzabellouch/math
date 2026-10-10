import OAI.NumberTheory.Ostmann.Construction.PhysicalAmplificationBudget

namespace OAI

/-! # A fixed kernel bias survives distinct-tuple amplification -/

namespace Ostmann

open Filter

theorem eventual_kernel_amplification_margin (c : ℝ) (hc : 0 < c) :
    ∀ᶠ T : ℝ in atTop, ∀ (r : ℕ) (J : ℝ),
      (r : ℝ) ≤ 2 * T ^ (3 / 5 : ℝ) → Real.exp (3 * T / 5) ≤ J →
      Real.exp (-T / 10) ≤ c ^ r ∧
      0 < c ^ r - (r : ℝ) ^ 2 / J ∧
      (c ^ r - (r : ℝ) ^ 2 / J)⁻¹ ^ 2 ≤ Real.exp T := by
  have hpoly := ((isLittleO_pow_exp_pos_mul_atTop 2 (show (0 : ℝ) < 1 / 2 by norm_num)).const_mul_left 8).bound
    (show (0 : ℝ) < 1 by norm_num)
  filter_upwards [eventual_amplification_log_loss |Real.log c| (1 / 10) (abs_nonneg _) (by norm_num),
    hpoly, eventually_ge_atTop (5 : ℝ)] with T hlog hp hT r J hr hJ
  have hT1 : 1 ≤ T := by linarith
  have hTpos : 0 < T := by linarith
  have hK : T ^ (9999999 / 10000000 : ℝ) / 1000 ≤ T := by
    have hh : T ^ (9999999 / 10000000 : ℝ) ≤ T := by
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hT1
        (show (9999999 / 10000000 : ℝ) ≤ 1 by norm_num)
    linarith [Real.rpow_nonneg hTpos.le (9999999 / 10000000 : ℝ)]
  have hl := hlog r T (Nat.cast_nonneg _) hr hK
  have hlower : -T / 10 ≤ (r : ℝ) * Real.log c := by
    have hh := mul_le_mul_of_nonneg_left (neg_abs_le (Real.log c)) (Nat.cast_nonneg (α := ℝ) r)
    nlinarith [Real.log_nonneg hT1, abs_nonneg (Real.log c)]
  have hcPow : Real.exp (-T / 10) ≤ c ^ r := by
    have hh := Real.exp_le_exp.mpr hlower
    rwa [Real.exp_nat_mul, Real.exp_log hc] at hh
  have hJpos : 0 < J := (Real.exp_pos _).trans_le hJ
  have hrT : (r : ℝ) ≤ 2 * T := hr.trans (by
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hT1
      (show (3 / 5 : ℝ) ≤ 1 by norm_num))
  have hp' : 8 * T ^ 2 ≤ Real.exp (T / 2) := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ 8 * T ^ 2),
      abs_of_pos (Real.exp_pos _), one_mul, one_div, inv_mul_eq_div] using hp
  have herror : 2 * (r : ℝ) ^ 2 / J ≤ Real.exp (-T / 10) := by
    apply (div_le_iff₀ hJpos).mpr
    calc
      _ ≤ 8 * T ^ 2 := by nlinarith [Nat.cast_nonneg (α := ℝ) r]
      _ ≤ Real.exp (T / 2) := hp'
      _ = Real.exp (-T / 10) * Real.exp (3 * T / 5) := by rw [← Real.exp_add]; congr 1; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hJ (Real.exp_nonneg _)
  have hgap : Real.exp (-T / 10) / 2 ≤ c ^ r - (r : ℝ) ^ 2 / J := by
    have he : 2 * ((r : ℝ) ^ 2 / J) ≤ Real.exp (-T / 10) := by simpa only [mul_div_assoc] using herror
    linarith
  have hgapPos : 0 < c ^ r - (r : ℝ) ^ 2 / J := (by positivity : 0 < Real.exp (-T / 10) / 2).trans_le hgap
  refine ⟨hcPow, hgapPos, ?_⟩
  have hinv : (c ^ r - (r : ℝ) ^ 2 / J)⁻¹ ≤ 2 * Real.exp (T / 10) := by
    have hi := one_div_le_one_div_of_le (by positivity : 0 < Real.exp (-T / 10) / 2) hgap
    have he : 1 / (Real.exp (-T / 10) / 2) = 2 * Real.exp (T / 10) := by
      rw [show -T / 10 = -(T / 10) by ring, Real.exp_neg]
      field_simp
    simpa only [one_div, he] using hi
  calc
    _ ≤ (2 * Real.exp (T / 10)) ^ 2 := pow_le_pow_left₀ (inv_nonneg.mpr hgapPos.le) hinv 2
    _ = 4 * Real.exp (T / 5) := by
      rw [mul_pow, show (2 : ℝ) ^ 2 = 4 by norm_num, ← Real.exp_nat_mul]
      congr 2
      norm_num
      ring
    _ ≤ Real.exp (4 * T / 5) * Real.exp (T / 5) := by
      apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
      linarith [Real.add_one_le_exp (4 * T / 5)]
    _ = Real.exp T := by rw [← Real.exp_add]; congr 1; ring

end Ostmann

end OAI
