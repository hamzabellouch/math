import OAI.NumberTheory.Ostmann.Construction.FinalHistoryCorrelations
import OAI.NumberTheory.Ostmann.Construction.OneSidedDecayBudget

namespace OAI

/-! # The finite-depth cost of summing both frequency histories -/

namespace Ostmann

open scoped BigOperators
open Filter

theorem card_frequencyTree (A : Type) [Fintype A] (n : ℕ) :
    Fintype.card (FrequencyTree A n) = (Fintype.card A) ^ (2 ^ (n + 1) - 1) := by
  induction n with
  | zero => simp [FrequencyTree]
  | succ n ih =>
    simp only [FrequencyTree, Fintype.card_prod] at *
    rw [ih, ← pow_add, ← pow_succ']
    congr 1
    have hp : 1 ≤ 2 ^ (n + 1) := Nat.one_le_two_pow
    rw [pow_succ]
    omega

theorem frequency_history_pair_card_bound (S : Finset ℤ) (n : ℕ) (C m : ℝ)
    (hS : (S.card : ℝ) ≤ Real.exp (C * m)) :
    ((Fintype.card (FrequencyTree S n) : ℝ) ^ 2) ≤
      Real.exp ((2 * (2 ^ (n + 1) - 1 : ℕ) : ℝ) * C * m) := by
  rw [card_frequencyTree]
  simp only [Fintype.card_coe]
  push_cast
  rw [← pow_mul]
  have h := pow_le_pow_left₀ (Nat.cast_nonneg S.card) hS ((2 ^ (n + 1) - 1) * 2)
  rw [← Real.exp_nat_mul] at h
  convert h using 1
  congr 1
  push_cast
  ring

/-- Double-exponential cancellation survives both full finite-depth
frequency sums. The depth and the frequency exponent are fixed first. -/
theorem eventual_history_pair_decay (n : ℕ) (C z α c : ℝ)
    (hC : 0 ≤ C) (hz : 0 ≤ z) (hα : 0 < α) (hc : 0 < c) :
    ∀ᶠ L : ℝ in atTop, ∀ (m : ℝ) (S : Finset ℤ), 0 ≤ m → m ≤ z * L →
      (S.card : ℝ) ≤ Real.exp (C * m) →
      (Fintype.card (FrequencyTree S n) : ℝ) ^ 2 * Real.exp (-c * Real.exp (α * L)) ≤
        Real.exp (-(c / 2) * Real.exp (α * L)) := by
  let A : ℝ := (2 * (2 ^ (n + 1) - 1 : ℕ) : ℝ) * C
  have hA : 0 ≤ A := mul_nonneg (by positivity) hC
  filter_upwards [eventual_polynomial_log_budget A z α (c / 2) 1 hA hz hα (by positivity)]
    with L hL m S hm hmL hS
  have hb := hL m hm hmL
  simp only [pow_one] at hb
  have hcard := frequency_history_pair_card_bound S n C m hS
  calc
    _ ≤ Real.exp (A * m) * Real.exp (-c * Real.exp (α * L)) := by
      exact mul_le_mul_of_nonneg_right hcard (Real.exp_nonneg _)
    _ ≤ _ := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      nlinarith

end Ostmann

end OAI
