import OAI.NumberTheory.Ostmann.Arithmetic.MovingPatternUniformBudget

namespace OAI

/-! # Equality-pattern costs for two prime giants -/

namespace Ostmann
open scoped Classical BigOperators

theorem movingPattern_prime_loss_le (n r : ℕ) (hr : r ≤ 4 * n * 2 ^ n)
    (E : ℝ) (hE : 0 ≤ E) :
    (4 : ℝ) ^ r * E ^ (4 * n * 2 ^ n - r) ≤
      (max 4 E) ^ (4 * n * 2 ^ n) := by
  have hK : 0 ≤ max (4 : ℝ) E := (by norm_num : (0 : ℝ) ≤ 4).trans (le_max_left _ _)
  calc
    _ ≤ (max 4 E) ^ r * (max 4 E) ^ (4 * n * 2 ^ n - r) :=
      mul_le_mul (pow_le_pow_left₀ (by norm_num) (le_max_left _ _) r)
        (pow_le_pow_left₀ hE (le_max_right _ _) _) (by positivity) (pow_nonneg hK _)
    _ = _ := by rw [← pow_add, Nat.add_sub_of_le hr]

/-- Summing every original equality pattern introduces only a depth-dependent
factor. The number of protected bulk slots never appears in this cost. -/
theorem movingPattern_prime_error_sum_le (n : ℕ) (E D : ℝ) (hE : 0 ≤ E) (hD : 0 ≤ D) :
    letI := sampleSetoidFintype (Bool × MovingSampleIndex n)
    ∀ R : Setoid (Bool × MovingSampleIndex n) → ℂ,
      (∀ s, ‖R s‖ ≤ D * ((4 : ℝ) ^ Fintype.card (Quotient s) *
        E ^ (4 * n * 2 ^ n - Fintype.card (Quotient s)))) →
      ‖∑ s, R s‖ ≤ (2 : ℝ) ^ ((4 * n * 2 ^ n) ^ 2) *
        (D * (max 4 E) ^ (4 * n * 2 ^ n)) := by
  let _ := sampleSetoidFintype (Bool × MovingSampleIndex n)
  intro R hR
  have hp := movingSamplePair_pattern_count n
  dsimp only at hp
  have hcard : (Fintype.card (Setoid (Bool × MovingSampleIndex n)) : ℝ) ≤
      (2 : ℝ) ^ ((4 * n * 2 ^ n) ^ 2) := by exact_mod_cast hp
  calc
    ‖∑ s, R s‖ ≤ ∑ s, ‖R s‖ := norm_sum_le _ _
    _ ≤ ∑ _s : Setoid (Bool × MovingSampleIndex n), D * (max 4 E) ^ (4 * n * 2 ^ n) := by
      apply Finset.sum_le_sum
      intro s _
      exact (hR s).trans (mul_le_mul_of_nonneg_left
        (movingPattern_prime_loss_le n _ (movingPattern_quotient_card_le n s) E hE) hD)
    _ = (Fintype.card (Setoid (Bool × MovingSampleIndex n)) : ℝ) *
        (D * (max 4 E) ^ (4 * n * 2 ^ n)) := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right hcard (by positivity)

end Ostmann

end OAI
