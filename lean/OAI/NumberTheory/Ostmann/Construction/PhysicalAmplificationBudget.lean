import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import OAI.NumberTheory.Ostmann.Construction.PhysicalAmplification

namespace OAI

/-! # The original amplification dominates all fixed-bias and tail losses -/

namespace Ostmann

open Filter Asymptotics

theorem eventual_amplification_log_loss (C ε : ℝ) (hC : 0 ≤ C) (hε : 0 < ε) :
    ∀ᶠ T : ℝ in atTop, ∀ k K : ℝ,
      0 ≤ k → k ≤ 2 * T ^ (3 / 5 : ℝ) →
      T ^ (9999999 / 10000000 : ℝ) / 1000 ≤ K →
      C * (1 + k) + 6 * Real.log T ≤ ε * K := by
  let D := 3 * C + 6
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hl := (isLittleO_log_rpow_atTop (show (0 : ℝ) < 3 / 5 by norm_num)).bound zero_lt_one
  have hp := (tendsto_rpow_atTop
    (show (0 : ℝ) < 9999999 / 10000000 - 3 / 5 by norm_num)).eventually_ge_atTop
    (1000 * D / ε)
  filter_upwards [hl, hp, eventually_ge_atTop (1 : ℝ)] with T hlog hpow hT k K hk hkU hK
  have hTpos : 0 < T := by linarith
  have hlog' : Real.log T ≤ T ^ (3 / 5 : ℝ) := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg hT),
      abs_of_nonneg (Real.rpow_nonneg hTpos.le _), one_mul] using hlog
  have h1 : (1 : ℝ) ≤ T ^ (3 / 5 : ℝ) := Real.one_le_rpow hT (by norm_num)
  have hb : C * (1 + k) + 6 * Real.log T ≤ D * T ^ (3 / 5 : ℝ) := by
    have hc := mul_le_mul_of_nonneg_left h1 hC
    have hkc := mul_le_mul_of_nonneg_left hkU hC
    dsimp [D]
    nlinarith only [hc, hkc, hlog']
  have hp' := (div_le_iff₀ hε).mp hpow
  have hh := mul_le_mul_of_nonneg_right hp' (Real.rpow_nonneg hTpos.le (3 / 5 : ℝ))
  have he : (T ^ (9999999 / 10000000 - 3 / 5 : ℝ) * ε) * T ^ (3 / 5 : ℝ) =
      ε * T ^ (9999999 / 10000000 : ℝ) := by
    rw [mul_right_comm, ← Real.rpow_add hTpos]
    norm_num
    ring
  rw [he] at hh
  have hK' := mul_le_mul_of_nonneg_left hK hε.le
  have hb' : D * T ^ (3 / 5 : ℝ) ≤ ε * K := by nlinarith only [hh, hK']
  exact hb.trans hb'

theorem eventual_physical_amplification_factor (a c : ℝ) (ha : 0 < a) (hc : 0 < c) :
    ∀ᶠ T : ℝ in atTop, ∀ (k : ℕ) (K : ℝ),
      (k : ℝ) ≤ 2 * T ^ (3 / 5 : ℝ) →
      T ^ (9999999 / 10000000 : ℝ) / 1000 ≤ K →
      Real.exp ((2 / 125 : ℝ) * K) ≤ a * Real.exp (K / 50) * c ^ k / T ^ 6 := by
  let C := |Real.log a| + |Real.log c|
  have hC : 0 ≤ C := by dsimp [C]; positivity
  filter_upwards [eventual_amplification_log_loss C (1 / 250) hC (by norm_num),
    eventually_ge_atTop (1 : ℝ)] with T hbudget hT k K hk hK
  have hTpos : 0 < T := by linarith
  have hb := hbudget k K (Nat.cast_nonneg _) hk hK
  have hl : -(K / 250) ≤ Real.log a + (k : ℝ) * Real.log c - 6 * Real.log T := by
    have ha' := neg_abs_le (Real.log a)
    have hc' := mul_le_mul_of_nonneg_left (neg_abs_le (Real.log c)) (Nat.cast_nonneg k)
    have hka := mul_nonneg (abs_nonneg (Real.log a)) (Nat.cast_nonneg (α := ℝ) k)
    dsimp [C] at hb
    nlinarith only [hb, ha', hc', hka, abs_nonneg (Real.log c)]
  have he := Real.exp_le_exp.mpr hl
  have hid : Real.exp (Real.log a + (k : ℝ) * Real.log c - 6 * Real.log T) =
      a * c ^ k / T ^ 6 := by
    rw [Real.exp_sub, Real.exp_add, Real.exp_log ha, Real.exp_nat_mul,
      Real.exp_log hc]
    have hden : Real.exp (6 * Real.log T) = T ^ 6 := by
      simpa only [Nat.cast_ofNat, Real.exp_log hTpos] using Real.exp_nat_mul (Real.log T) 6
    rw [hden]
  rw [hid] at he
  have hm := mul_le_mul_of_nonneg_left he (Real.exp_nonneg (K / 50))
  have hleft : Real.exp (K / 50) * Real.exp (-(K / 250)) =
      Real.exp ((2 / 125 : ℝ) * K) := by rw [← Real.exp_add]; congr 1; ring
  rw [hleft] at hm
  convert hm using 1
  ring

end Ostmann

end OAI
