import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

namespace OAI

/-! # The gain on the middle interval absorbs all three density losses -/

namespace Falconer
open scoped ENNReal

theorem three_interval_radial_power (g₀ g₁ g₂ N : ℕ) (hsum : g₀+g₁+g₂ = N)
    {q c β γ e₀ e₂ η : ℝ} (hc : 0 ≤ c)
    (hwidth : β*(N:ℝ) ≤ g₁) (hbudget : e₀+e₂+3*η+γ ≤ c*β) :
    ((2:ℝ)^N)^(e₀+e₂+3*η)*((2:ℝ)^g₀)^(-q)*
      ((2:ℝ)^g₁)^(-q-c)*((2:ℝ)^g₂)^(-q) ≤ ((2:ℝ)^N)^(-q-γ) := by
  have hp (n : ℕ) (t : ℝ) : ((2:ℝ)^n)^t = (2:ℝ)^((n:ℝ)*t) :=
    (Real.rpow_natCast_mul (by norm_num : (0:ℝ) ≤ 2) n t).symm
  simp_rw [hp,← Real.rpow_add (by norm_num : (0:ℝ) < 2)]
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2)
  have hn : (0:ℝ) ≤ N := Nat.cast_nonneg N
  have hsum' : (g₀:ℝ)+g₁+g₂ = N := by exact_mod_cast hsum
  nlinarith [congrArg (fun z : ℝ => z*q) hsum',
    mul_le_mul_of_nonneg_left hbudget hn,mul_le_mul_of_nonneg_left hwidth hc]

end Falconer

end OAI
