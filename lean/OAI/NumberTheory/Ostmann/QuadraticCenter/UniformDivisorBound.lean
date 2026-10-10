import Mathlib.Analysis.SpecialFunctions.Log.Basic
import OAI.NumberTheory.Ostmann.Preliminaries.DivisorPowerBound

namespace OAI

/-! # Uniform subexponential divisor loss on the arithmetic moduli -/

namespace Ostmann

theorem divisors_subexponential_uniform (C ε : ℝ) (hC : 0 ≤ C) (hε : 0 < ε) :
    ∃ M : ℝ, ∀ m : ℝ, M ≤ m → ∀ n : ℕ, n ≠ 0 → (n : ℝ) ≤ Real.exp (C * m) →
      (n.divisors.card : ℝ) ≤ Real.exp (ε * m) := by
  obtain ⟨k, hk⟩ := exists_nat_gt (C / ε)
  have hgap : 0 < ε * k - C := by
    have h := (div_lt_iff₀ hε).mp hk
    nlinarith
  have hk0 : k ≠ 0 := by
    intro hz
    simp only [hz, Nat.cast_zero, mul_zero] at hgap
    linarith
  obtain ⟨D, hD, hbound⟩ := exists_divisors_power_bound k
  have hDpos : (0 : ℝ) < D := by exact_mod_cast (show 0 < D from hD)
  refine ⟨Real.log D / (ε * k - C), fun m hm n hn hnupper => ?_⟩
  have hlog : Real.log D + C * m ≤ ε * k * m := by
    have h := (div_le_iff₀ hgap).mp hm
    nlinarith
  have hpower : (n.divisors.card : ℝ) ^ k ≤ Real.exp (ε * m) ^ k := by
    calc
      _ ≤ (D : ℝ) * n := by exact_mod_cast hbound n hn
      _ ≤ (D : ℝ) * Real.exp (C * m) := mul_le_mul_of_nonneg_left hnupper hDpos.le
      _ = Real.exp (Real.log D + C * m) := by rw [Real.exp_add, Real.exp_log hDpos]
      _ ≤ Real.exp (ε * k * m) := Real.exp_le_exp.mpr hlog
      _ = _ := by rw [← Real.exp_nat_mul]; congr 1; ring
  exact (pow_le_pow_iff_left₀ (Nat.cast_nonneg _) (Real.exp_pos _).le hk0).mp hpower

end Ostmann

end OAI
