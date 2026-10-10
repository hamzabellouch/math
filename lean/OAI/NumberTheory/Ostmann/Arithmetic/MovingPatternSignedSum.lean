import OAI.NumberTheory.Ostmann.Arithmetic.MovingPatternUniformBudget

namespace OAI

/-! # Summing the signed pattern bounds without a bulk-length loss -/

namespace Ostmann
open scoped Classical BigOperators

/-- The per-class comparison error and signed bulk remainder can be summed
across every equality pattern with a cost depending only on the fixed depth. -/
theorem movingPattern_signed_sum_bound (n : ℕ) (E D τ K : ℝ)
    (hE : 0 ≤ E) (hD : 0 ≤ D) (hτ : 0 ≤ τ) (hK : 0 ≤ K) :
    let _ := sampleSetoidFintype (Bool × MovingSampleIndex n)
    ∀ R : Setoid (Bool × MovingSampleIndex n) → ℂ,
      (∀ s, ‖R s‖ ≤
        ((2 : ℝ) ^ Fintype.card (Quotient s) *
          E ^ (4 * n * 2 ^ n - Fintype.card (Quotient s))) *
          (D * Fintype.card (Quotient s) * τ + K)) →
      ‖∑ s, R s‖ ≤ (2 : ℝ) ^ ((4 * n * 2 ^ n) ^ 2) *
        ((D * (4 * n * 2 ^ n : ℕ) * τ + K) * (max 2 E) ^ (4 * n * 2 ^ n)) := by
  dsimp only
  let _ := sampleSetoidFintype (Bool × MovingSampleIndex n)
  intro R hR
  apply movingPattern_error_sum_le n E (D * (4 * n * 2 ^ n : ℕ) * τ + K) hE (by positivity) R
  intro s
  have hc : (Fintype.card (Quotient s) : ℝ) ≤ (4 * n * 2 ^ n : ℕ) := by
    exact_mod_cast movingPattern_quotient_card_le n s
  have hcost : D * Fintype.card (Quotient s) * τ + K ≤ D * (4 * n * 2 ^ n : ℕ) * τ + K :=
    add_le_add (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hc hD) hτ) le_rfl
  exact (hR s).trans ((mul_le_mul_of_nonneg_left hcost (by positivity)).trans_eq (mul_comm _ _))

end Ostmann

end OAI
