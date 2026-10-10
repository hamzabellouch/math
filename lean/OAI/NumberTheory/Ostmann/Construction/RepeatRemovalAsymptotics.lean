import OAI.NumberTheory.Ostmann.Construction.RepeatRemovalBudget

namespace OAI

/-! # The chosen prime population makes the relative deletion error small -/

namespace Ostmann

open Filter Asymptotics

theorem eventual_repeat_power_budget (C ε : ℝ) (hC : 1 ≤ C) (hε : 0 < ε) :
    ∀ᶠ T : ℝ in atTop, ∀ (k : ℕ) (K : ℝ),
      (k : ℝ) ≤ 2 * T ^ (3 / 5 : ℝ) →
      T ^ (9999999 / 10000000 : ℝ) / 1000 ≤ K →
      (16 * C * T * (k : ℝ) ^ 3) ^ k * C ^ 2 ≤ Real.exp (ε * K) := by
  let B := 128 * C
  let D := 2 * B + 8 + 2 * C
  have hC0 : 0 ≤ C := by linarith
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hl := (isLittleO_log_rpow_atTop (show (0 : ℝ) < 1 / 10 by norm_num)).bound zero_lt_one
  have hp := (tendsto_rpow_atTop
    (show (0 : ℝ) < 9999999 / 10000000 - 7 / 10 by norm_num)).eventually_ge_atTop
    (1000 * D / ε)
  filter_upwards [hl, hp, eventually_ge_atTop (1 : ℝ)] with T hlog hpow hT k K hk hK
  have hTpos : 0 < T := by linarith
  have hlogT : 0 ≤ Real.log T := Real.log_nonneg hT
  have hlog' : Real.log T ≤ T ^ (1 / 10 : ℝ) := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg hlogT,
      abs_of_nonneg (Real.rpow_nonneg hTpos.le _), one_mul] using hlog
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg _
  have hρ : T ^ (3 / 5 : ℝ) ≤ T := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hT (show (3 / 5 : ℝ) ≤ 1 by norm_num)
  have hkT : (k : ℝ) ≤ 2 * T := hk.trans (by gcongr)
  have hbase : 16 * C * T * (k : ℝ) ^ 3 ≤ Real.exp (B + 4 * Real.log T) := by
    calc
      _ ≤ 16 * C * T * (2 * T) ^ 3 := by gcongr
      _ = B * T ^ 4 := by dsimp [B]; ring
      _ ≤ Real.exp B * T ^ 4 := by gcongr; linarith [Real.add_one_le_exp B]
      _ = Real.exp (B + 4 * Real.log T) := by
        rw [Real.exp_add]
        congr 1
        simpa only [Nat.cast_ofNat, Real.exp_log hTpos] using
          (Real.exp_nat_mul (Real.log T) 4).symm
  have hklog : (k : ℝ) * Real.log T ≤ 2 * T ^ (7 / 10 : ℝ) := by
    calc
      _ ≤ (2 * T ^ (3 / 5 : ℝ)) * T ^ (1 / 10 : ℝ) :=
        mul_le_mul hk hlog' hlogT (by positivity)
      _ = _ := by rw [mul_assoc, ← Real.rpow_add hTpos]; norm_num
  have hρ' : T ^ (3 / 5 : ℝ) ≤ T ^ (7 / 10 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hT (by norm_num)
  have h1 : (1 : ℝ) ≤ T ^ (7 / 10 : ℝ) := Real.one_le_rpow hT (by norm_num)
  have hexp : (k : ℝ) * (B + 4 * Real.log T) + 2 * C ≤ D * T ^ (7 / 10 : ℝ) := by
    have hk7 : (k : ℝ) ≤ 2 * T ^ (7 / 10 : ℝ) :=
      hk.trans (mul_le_mul_of_nonneg_left hρ' (by norm_num))
    have hkb := mul_le_mul_of_nonneg_left hk7 hB
    have hc := mul_le_mul_of_nonneg_left h1 (show 0 ≤ 2 * C by positivity)
    dsimp [D]
    nlinarith only [hkb, hc, hklog]
  have hbudget : D * T ^ (7 / 10 : ℝ) ≤ ε * K := by
    have hp' := (div_le_iff₀ hε).mp hpow
    have hh := mul_le_mul_of_nonneg_right hp' (Real.rpow_nonneg hTpos.le (7 / 10 : ℝ))
    have heq : T ^ (9999999 / 10000000 - 7 / 10 : ℝ) * T ^ (7 / 10 : ℝ) =
        T ^ (9999999 / 10000000 : ℝ) := by
      rw [← Real.rpow_add hTpos]
      norm_num
    have heq' : (T ^ (9999999 / 10000000 - 7 / 10 : ℝ) * ε) * T ^ (7 / 10 : ℝ) =
        ε * T ^ (9999999 / 10000000 : ℝ) := by rw [mul_right_comm, heq, mul_comm]
    rw [heq'] at hh
    have hK' := mul_le_mul_of_nonneg_left hK hε.le
    nlinarith only [hh, hK']
  calc
    _ ≤ (Real.exp (B + 4 * Real.log T)) ^ k * (Real.exp C) ^ 2 := by
      apply mul_le_mul (pow_le_pow_left₀ (by positivity) hbase k) _ (sq_nonneg C) (by positivity)
      exact pow_le_pow_left₀ hC0 (by linarith [Real.add_one_le_exp C]) 2
    _ = Real.exp ((k : ℝ) * (B + 4 * Real.log T) + 2 * C) := by
      rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add]
      norm_num
    _ ≤ _ := Real.exp_le_exp.mpr (hexp.trans hbudget)

end Ostmann

end OAI
