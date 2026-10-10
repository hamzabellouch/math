import OAI.NumberTheory.Ostmann.Construction.ScheduledHistoryError
import OAI.NumberTheory.Ostmann.Construction.FactorialExponential
import OAI.NumberTheory.Ostmann.Construction.ConstituentMatchedCostData

namespace OAI

/-! # All matching and frequency sums preserve the small character error -/
namespace Ostmann
open Filter
open scoped Classical BigOperators

theorem factorial_le_exp_square (n : ℕ) :
    (n.factorial : ℝ) ≤ Real.exp ((n : ℝ) ^ 2) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · apply (factorial_exp_upper hn).trans
    apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_left (Real.log_le_self (Nat.cast_nonneg n)) (Nat.cast_nonneg n)]

theorem eventual_scheduled_matching_error (n : ℕ) (a C H T z α c : ℝ)
    (ha : 0 ≤ a) (hC : 0 ≤ C) (hH : 0 ≤ H) (hT : 0 ≤ T)
    (hz : 0 ≤ z) (hα : 0 < α) (hc : 0 < c) :
    ∀ᶠ L : ℝ in atTop, ∀ (J : Type*) [Fintype J] (M : ℝ)
      (V : ℕ → ℕ) (S : Finset (Equiv.Perm J)) (mass : J → ℝ),
      0 ≤ M → M ≤ z * L → (Fintype.card J : ℝ) ≤ a * (1 + M) →
      Monotone V → ((transferFrequencyRange (V n)).card : ℝ) ≤ Real.exp (C * (1 + M)) →
      (∀ j, 0 ≤ mass j) → (∀ j, mass j ≤ Real.exp (H * (1 + M))) →
      (S.card : ℝ) * (Fintype.card (ScheduledFrequencyIndex V n) : ℝ) ^ 2 *
        (∏ j, mass j) * Real.exp (-c * Real.exp (α * L)) ≤ Real.exp (-T * M) := by
  let D : ℝ := 2 * ((2 ^ (n + 1) - 1 : ℕ) : ℝ)
  let B := a ^ 2 + a * H + D * C
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  filter_upwards [eventual_polynomial_log_budget (B + T) z α c 2 (by positivity) hz hα hc]
    with L hL
  intro J _ M V S mass hM hML hcard hV hfreq hmass hmassupper
  have hp : 0 ≤ 1 + M := by linarith
  have hfact : (S.card : ℝ) ≤ Real.exp (a ^ 2 * (1 + M) ^ 2) := by
    have hcount : S.card ≤ (Fintype.card J).factorial := by
      simpa only [Fintype.card_perm] using Finset.card_le_univ S
    apply (Nat.cast_le.mpr hcount).trans
    apply (factorial_le_exp_square _).trans
    apply Real.exp_le_exp.mpr
    calc
      (Fintype.card J : ℝ) ^ 2 ≤ (a * (1 + M)) ^ 2 :=
        pow_le_pow_left₀ (Nat.cast_nonneg _) hcard 2
      _ = _ := by ring
  have hhist : (Fintype.card (ScheduledFrequencyIndex V n) : ℝ) ^ 2 ≤
      Real.exp (D * C * (1 + M) ^ 2) := by
    apply (scheduledFrequencyIndex_pair_card_bound V hV n C (1 + M) hfreq).trans
    apply Real.exp_le_exp.mpr
    change D * C * (1 + M) ≤ D * C * (1 + M) ^ 2
    apply mul_le_mul_of_nonneg_left _ (mul_nonneg hD hC)
    nlinarith [sq_nonneg M]
  have hprod : (∏ j, mass j) ≤ Real.exp (a * H * (1 + M) ^ 2) := by
    calc
      _ ≤ ∏ _j : J, Real.exp (H * (1 + M)) :=
        Finset.prod_le_prod₀ (fun j _ => hmass j) (fun j _ => hmassupper j)
      _ = Real.exp ((Fintype.card J : ℝ) * (H * (1 + M))) := by
        rw [Finset.prod_const, Finset.card_univ, ← Real.exp_nat_mul]
      _ ≤ _ := by
        apply Real.exp_le_exp.mpr
        calc
          _ ≤ (a * (1 + M)) * (H * (1 + M)) :=
            mul_le_mul_of_nonneg_right hcard (mul_nonneg hH hp)
          _ = _ := by ring
  have htotal : (S.card : ℝ) * (Fintype.card (ScheduledFrequencyIndex V n) : ℝ) ^ 2 *
      (∏ j, mass j) ≤ Real.exp (B * (1 + M) ^ 2) := by
    apply (mul_le_mul (mul_le_mul hfact hhist (sq_nonneg _) (Real.exp_nonneg _)) hprod
      (Finset.prod_nonneg fun j _ => hmass j) (by positivity)).trans_eq
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    dsimp [B]
    ring
  calc
    _ ≤ Real.exp (B * (1 + M) ^ 2) * Real.exp (-c * Real.exp (α * L)) :=
      mul_le_mul_of_nonneg_right htotal (Real.exp_nonneg _)
    _ ≤ _ := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have hh := hL M hM hML
      have ht : T * M ≤ T * (1 + M) ^ 2 := by
        apply mul_le_mul_of_nonneg_left _ hT
        nlinarith [sq_nonneg M]
      nlinarith

end Ostmann

end OAI
