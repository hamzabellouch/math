import OAI.NumberTheory.Ostmann.Construction.WordPeriodBudget
import OAI.NumberTheory.Ostmann.Construction.OneSidedDecayBudget

namespace OAI

/-! # The final history pair's actual modulus fits below the long-prime scale -/
namespace Ostmann
open Filter

theorem eventual_final_pair_period_scale (n : ℕ) (b C z β : ℝ)
    (hb : 0 ≤ b) (hC : 0 ≤ C) (hz : 0 ≤ z) (hβ : 0 < β) :
    ∀ᶠ L : ℝ in atTop, ∀ (m : ℝ) (B V A : ℕ) (t t' : FrequencyTree ℤ n),
      0 ≤ m → m ≤ z * L → (B : ℝ) ≤ b * (1 + m) →
      (V : ℝ) ≤ Real.exp (C * (1 + m)) →
      (∀ s ∈ allFrequencyList n t, s.natAbs ≤ V) →
      (∀ s ∈ allFrequencyList n t', s.natAbs ≤ V) →
      Real.exp (Real.exp (β * L)) ≤ (A : ℝ) →
      wordTransferFullPeriod n t B * wordTransferFullPeriod n t' B ≤ A := by
  have hK : 0 ≤ 2 * C * wordPeriodExponent n b := by
    unfold wordPeriodExponent
    positivity
  filter_upwards [eventual_polynomial_log_budget (2 * C * wordPeriodExponent n b)
    z β 1 (n + 2) hK hz hβ zero_lt_one] with L hL m B V A t t' hm hmL hB hV hf hf' hA
  have hleft := wordTransferFullPeriod_le_exp n t B V b C m hC hm hB hV hf
  have hright := wordTransferFullPeriod_le_exp n t' B V b C m hC hm hB hV hf'
  have hprod : ((wordTransferFullPeriod n t B * wordTransferFullPeriod n t' B : ℕ) : ℝ) ≤
      Real.exp (2 * C * wordPeriodExponent n b * (1 + m) ^ (n + 2)) := by
    push_cast
    calc
      _ ≤ Real.exp (C * wordPeriodExponent n b * (1 + m) ^ (n + 2)) *
          Real.exp (C * wordPeriodExponent n b * (1 + m) ^ (n + 2)) :=
        mul_le_mul hleft hright (Nat.cast_nonneg _) (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have he := hL m hm hmL
  simp only [one_mul] at he
  exact_mod_cast hprod.trans ((Real.exp_le_exp.mpr he).trans hA)

end Ostmann

end OAI
