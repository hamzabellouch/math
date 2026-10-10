import OAI.NumberTheory.Ostmann.Construction.ScheduledHistoryError
import OAI.NumberTheory.Ostmann.Construction.FinalExponentialContradiction

namespace OAI

/-! # The canonical history sum is negligible in the final factorial comparison -/
namespace Ostmann
open Filter

theorem eventual_scheduled_final_contradiction (n : ℕ) (B₁ D C δ z α c : ℝ)
    (hB₁ : 0 ≤ B₁) (hD : 0 ≤ D) (hδ : 0 < δ) (hz : 0 ≤ z)
    (hα : 0 < α) (hc : 0 < c)
    (hentropy : C + D + 2 * B₁ + δ ≤ (n : ℝ) * Real.log 2 - 1) :
    ∀ᶠ L : ℝ in atTop, ∀ (m : ℕ) (V : ℕ → ℕ) (η : ℂ),
      Monotone V → (m : ℝ) ≤ z * L →
      ((transferFrequencyRange (V (n + 1))).card : ℝ) ≤
        Real.exp (D * (2 ^ (n + 1) : ℝ) * m) →
      Real.log 2 < δ * (2 ^ (n + 1) : ℝ) * m →
      Real.exp (-B₁ * (2 ^ (n + 1) : ℝ) * m) ≤ ‖η‖ →
      ‖η‖ ^ 2 ≤ ((transferFrequencyRange (V (n + 1))).card : ℝ) *
        (Real.exp (C * (2 ^ (n + 1) : ℝ) * m) /
          (Fintype.card (FinalParityReassignments n m) : ℝ) +
        (Fintype.card (ScheduledFrequencyIndex V (n + 1)) : ℝ) ^ 2 *
          Real.exp (-c * Real.exp (α * L))) → False := by
  have hroot : 0 ≤ D * (2 ^ (n + 1) : ℝ) := by positivity
  have herror : 0 ≤ D + 2 * B₁ + δ := by positivity
  filter_upwards [eventual_scheduled_history_error (n + 1)
    (D * (2 ^ (n + 1) : ℝ)) (D + 2 * B₁ + δ) z α c hroot herror hz hα hc]
    with L hL m V η hV hm hcard hmargin hlower hcompare
  have herr := hL (m : ℝ) V hV (Nat.cast_nonneg m) hm (by simpa only [mul_assoc] using hcard)
  exact final_exponential_contradiction n m B₁ D C δ
    ((transferFrequencyRange (V (n + 1))).card : ℝ)
    (Real.exp (C * (2 ^ (n + 1) : ℝ) * m))
    ((Fintype.card (ScheduledFrequencyIndex V (n + 1)) : ℝ) ^ 2 *
      Real.exp (-c * Real.exp (α * L))) η hcard (Real.exp_nonneg _)
    (mul_nonneg (sq_nonneg _) (Real.exp_nonneg _)) le_rfl (by simpa only [Nat.cast_pow, Nat.cast_ofNat] using herr) hentropy hmargin hlower hcompare

theorem selected_prime_energy_exponent_le (n m : ℕ) (L A ε : ℝ)
    (hA : 0 ≤ A) (hε : 0 ≤ ε) (hL : L ≤ (m : ℝ)) :
    A * (2 ^ (n + 1) : ℝ) * L + ε * m ≤
      (A + ε) * (2 ^ (n + 1) : ℝ) * m := by
  have hr : (1 : ℝ) ≤ 2 ^ (n + 1) := one_le_pow₀ (by norm_num)
  have hmain := mul_le_mul_of_nonneg_left hL (mul_nonneg hA (by positivity : (0 : ℝ) ≤ 2 ^ (n + 1)))
  have hsmall := mul_le_mul_of_nonneg_left hr (mul_nonneg hε (Nat.cast_nonneg m))
  nlinarith

end Ostmann

end OAI
