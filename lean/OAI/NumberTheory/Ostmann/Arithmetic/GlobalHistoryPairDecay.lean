import OAI.NumberTheory.Ostmann.Arithmetic.GlobalHistoryPairBound
import OAI.NumberTheory.Ostmann.Characters.DyadicCharacterBudget

namespace OAI

/-! # Double-exponential decay of the constructed history-pair bound -/

namespace Ostmann

open scoped BigOperators
open Filter

theorem eventual_history_pair_numeric_bound (K z α β γ c : ℝ) (d : ℕ)
    (hK : 0 ≤ K) (hz : 0 ≤ z) (hα : 0 < α) (hαβ : α < β)
    (hγβ : γ < β) (hc : 0 < c) :
    ∀ᶠ L : ℝ in atTop, ∀ {V : Type} (D D' : HistoryCoefficientData V)
      (frequencies : List ℤ) (C A E : ℕ) (P Q : Finset ℕ) (lower : ℝ) (Bq : ℕ) (m : ℝ),
      0 ≤ m → m ≤ z * L →
      Real.exp (c * Real.exp (α * L)) ≤ lower →
      Real.exp (Real.exp (β * L)) ≤ (A : ℝ) →
      (Bq : ℝ) ≤ Real.exp (Real.exp (γ * L)) →
      2 * ((Nat.log 2 E + 1 : ℕ) : ℝ) * (∑ p ∈ P, (p : ℝ)⁻¹)⁻¹ *
        (∑ q ∈ Q, (q : ℝ)⁻¹)⁻¹ * (D.budget * D'.budget) ^ 2 ≤ Real.exp (K * (1 + m) ^ d) →
      2 * ((Nat.log 2 E + 1 : ℕ) : ℝ) * (∑ p ∈ P, (p : ℝ)⁻¹)⁻¹ *
        (historyFrequencyPeriod frequencies (C ^ (D.steps.length + D'.steps.length) + 1) : ℝ) *
        (3 ^ (2 * (D.complexity + D'.complexity)) : ℕ) * (D.budget * D'.budget) ^ 2 ≤
          Real.exp (K * (1 + m) ^ d) →
      historyPairBound D D' frequencies C A E P Q lower Bq ≤
        (Real.exp (-(c / 4) * Real.exp (α * L))) ^ 2 := by
  filter_upwards [eventual_one_sided_squared_budget K z α β γ c d hK hz hα hαβ hγβ hc]
    with L hL V D D' frequencies C A E P Q lower Bq m hm hmL hlower hA hBq hcost₁ hcost₂
  apply le_trans (dyadic_character_numeric_bound
    ((Nat.log 2 E + 1 : ℕ) : ℝ) (∑ p ∈ P, (p : ℝ)⁻¹)⁻¹ (∑ q ∈ Q, (q : ℝ)⁻¹)⁻¹
    (historyFrequencyPeriod frequencies (C ^ (D.steps.length + D'.steps.length) + 1))
    (3 ^ (2 * (D.complexity + D'.complexity)) : ℕ) (D.budget * D'.budget)
    A lower Bq (Real.exp (K * (1 + m) ^ d)) α β γ c L
    (by positivity) (by positivity) (by positivity) (by positivity) (by positivity)
    hlower hA (Nat.cast_nonneg Bq) hBq hcost₁ hcost₂)
  apply (hL m hm hmL).trans_eq
  rw [← Real.exp_nat_mul]
  congr 1
  ring

end Ostmann

end OAI
