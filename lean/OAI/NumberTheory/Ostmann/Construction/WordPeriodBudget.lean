import Mathlib.Analysis.SpecialFunctions.Exp
import OAI.NumberTheory.Ostmann.Construction.WordTransferFullPeriod

namespace OAI

/-! # Polynomial exponential bound for the actual common frequency period -/

namespace Ostmann

def wordPeriodExponent (n : ℕ) (b : ℝ) : ℝ :=
  ((2 ^ n - 1 : ℕ) : ℝ) * (b ^ (n + 1) + 1) + ((2 ^ (n + 1) - 1 : ℕ) : ℝ)

theorem wordTransferFullPeriod_le_exp (n : ℕ) (t : FrequencyTree ℤ n) (B V : ℕ)
    (b C m : ℝ) (hC : 0 ≤ C) (hm : 0 ≤ m)
    (hB : (B : ℝ) ≤ b * (1 + m)) (hV : (V : ℝ) ≤ Real.exp (C * (1 + m)))
    (hf : ∀ s ∈ allFrequencyList n t, s.natAbs ≤ V) :
    (wordTransferFullPeriod n t B : ℝ) ≤
      Real.exp (C * wordPeriodExponent n b * (1 + m) ^ (n + 2)) := by
  let e := (2 ^ n - 1) * (B ^ (n + 1) + 1) + (2 ^ (n + 1) - 1)
  have hr : 0 ≤ 1 + m := by linarith
  have hr1 : 1 ≤ (1 + m) ^ (n + 1) := one_le_pow₀ (by linarith)
  have hbp : (B : ℝ) ^ (n + 1) ≤ b ^ (n + 1) * (1 + m) ^ (n + 1) := by
    simpa only [mul_pow] using pow_le_pow_left₀ (Nat.cast_nonneg B) hB (n + 1)
  have he : (e : ℝ) ≤ wordPeriodExponent n b * (1 + m) ^ (n + 1) := by
    dsimp [e, wordPeriodExponent]
    push_cast
    calc
      _ ≤ ((2 ^ n - 1 : ℕ) : ℝ) * ((b ^ (n + 1) + 1) * (1 + m) ^ (n + 1)) +
          ((2 ^ (n + 1) - 1 : ℕ) : ℝ) * (1 + m) ^ (n + 1) := by
        exact add_le_add
          (mul_le_mul_of_nonneg_left (by nlinarith only [hbp, hr1]) (Nat.cast_nonneg _))
          (le_mul_of_one_le_right (Nat.cast_nonneg _) hr1)
      _ = _ := by ring
  have hnat : (wordTransferFullPeriod n t B : ℝ) ≤ (V : ℝ) ^ e := by
    exact_mod_cast wordTransferFullPeriod_le n t B V hf
  calc
    _ ≤ (V : ℝ) ^ e := hnat
    _ ≤ (Real.exp (C * (1 + m))) ^ e :=
      pow_le_pow_left₀ (Nat.cast_nonneg V) hV e
    _ = Real.exp ((e : ℝ) * (C * (1 + m))) := (Real.exp_nat_mul _ e).symm
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      have hh := mul_le_mul_of_nonneg_left he (mul_nonneg hC hr)
      calc
        _ = (C * (1 + m)) * e := by ring
        _ ≤ (C * (1 + m)) * (wordPeriodExponent n b * (1 + m) ^ (n + 1)) := hh
        _ = _ := by rw [pow_succ]; ring

end Ostmann

end OAI
