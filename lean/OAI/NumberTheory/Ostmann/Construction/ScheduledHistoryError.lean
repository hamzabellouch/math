import OAI.NumberTheory.Ostmann.Construction.ScheduledFrequencyBounds

namespace OAI

/-! # Both actual history sums preserve double-exponential cancellation -/

namespace Ostmann
open Filter

theorem eventual_scheduled_history_error (n : ℕ) (C H z α c : ℝ)
    (hC : 0 ≤ C) (hH : 0 ≤ H) (hz : 0 ≤ z) (hα : 0 < α) (hc : 0 < c) :
    ∀ᶠ L : ℝ in atTop, ∀ (m : ℝ) (V : ℕ → ℕ), Monotone V →
      0 ≤ m → m ≤ z * L →
      ((transferFrequencyRange (V n)).card : ℝ) ≤ Real.exp (C * m) →
      (Fintype.card (ScheduledFrequencyIndex V n) : ℝ) ^ 2 *
        Real.exp (-c * Real.exp (α * L)) ≤ Real.exp (-H * (2 ^ n : ℕ) * m) := by
  let A : ℝ := ((2 * (2 ^ (n + 1) - 1) : ℕ) : ℝ) * C
  have hA : 0 ≤ A := mul_nonneg (by positivity) hC
  have htotal : 0 ≤ A + H * (2 ^ n : ℕ) := by positivity
  filter_upwards [eventual_polynomial_log_budget (A + H * (2 ^ n : ℕ)) z α c 1
    htotal hz hα hc] with L hL
  intro m V hV hm hmL hS
  have hpoly := hL m hm hmL
  simp only [pow_one] at hpoly
  have hcard := scheduledFrequencyIndex_pair_card_bound V hV n C m hS
  have hcard' : (Fintype.card (ScheduledFrequencyIndex V n) : ℝ) ^ 2 ≤ Real.exp (A * m) := by
    simpa only [A, Nat.cast_mul, Nat.cast_ofNat, mul_assoc] using hcard
  calc
    _ ≤ Real.exp (A * m) * Real.exp (-c * Real.exp (α * L)) :=
      mul_le_mul_of_nonneg_right hcard' (Real.exp_pos _).le
    _ ≤ _ := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      nlinarith

end Ostmann

end OAI
