import OAI.NumberTheory.Ostmann.Arithmetic.MovingPatternBulkMean

namespace OAI

/-! # Integrating nonuniform errors under the original pattern law -/

namespace Ostmann
open scoped Classical BigOperators

theorem movingPattern_flagged_pointwise_bound {A B C : Type*}
    [Fintype B] [Fintype C] {N : ℕ}
    (e : Fin (N + 1) ≃ B ⊕ C) (μ : ℕ → A → ℝ) (ν : B → A → ℝ) (prime : A → ℕ)
    (n : ℕ) (t : Bool → FrequencyTree ℤ n) (small bulk : Bool → TreeLeafTuple (List B) n)
    (pattern : Bool × MovingSampleIndex n → C)
    (rep : ∀ c, {i : Bool × MovingSampleIndex n // pattern i = c}) (E : ℝ)
    (hprime : ∀ a, (prime a).Prime) (hμ : ∀ j a, 0 ≤ μ j a) (hν : ∀ j a, 0 ≤ ν j a)
    (hbound : ∀ j a, (prime a : ℝ) * μ j a ≤ E)
    (G : (Fin (N + 1) → A) → ℂ) (x : Fin (N + 1) → A) :
    ‖movingOriginalPatternWeight e μ ν prime n pattern G x *
      movingPatternFlagProduct e prime n t small bulk pattern rep x‖ ≤
      (‖G x‖ * ((2 : ℝ) ^ Fintype.card C * E ^ (4 * n * 2 ^ n - Fintype.card C))) *
        productPrior (fun i => Sum.elim ν (fun c => μ (movingSampleTier (rep c).val.2)) (e i)) x := by
  have h := movingPattern_flagged_weight_bound e μ ν prime n t small bulk pattern rep E hprime hμ hν hbound
    (fun _ => G x) ‖G x‖ (norm_nonneg _) (fun _ => le_rfl) x
  by_cases hi : Function.Injective (fun c => x (e.symm (.inr c))) <;>
    simpa only [movingOriginalPatternWeight, movingPatternInjectionGuard, hi, ite_true, ite_false] using h

/-- A variable bound for the literal signed bulk mean is integrated against
the original external and representative priors. In particular the large
pointwise spectator error is averaged, rather than replaced by its supremum. -/
theorem movingPattern_signed_bulk_majorant {A B C : Type*}
    [Fintype A] [Fintype B] [Fintype C] {N n m : ℕ}
    (e : Fin (N + 1) ≃ B ⊕ C) (μ : ℕ → A → ℝ) (ν : B → A → ℝ) (prime : A → ℕ)
    (t : Bool → FrequencyTree ℤ n) (small : Bool → TreeLeafTuple (List B) n)
    (slot : (TreeLeafIndex n × Fin m) ↪ B) (perm : Equiv.Perm (TreeLeafIndex n × Fin m))
    (pattern : Bool × MovingSampleIndex n → C)
    (rep : ∀ c, {i : Bool × MovingSampleIndex n // pattern i = c}) (E : ℝ) (hE : 0 ≤ E)
    (hprime : ∀ a, (prime a).Prime) (hμ : ∀ j a, 0 ≤ μ j a) (hν : ∀ j a, 0 ≤ ν j a)
    (hnmass : ∀ j, ∑ a, ν j a = 1)
    (hbound : ∀ j a, (prime a : ℝ) * μ j a ≤ E)
    (G : (Fin (N + 1) → A) → ℂ) (D : (Fin (N + 1) → A) → ℝ)
    (hG : ∀ x, ‖movingPatternBulkMean e ν slot G x‖ ≤ D x)
    (seed : TreeLeafIndex n × Fin m → A) :
    let law := fun i => Sum.elim ν (fun c => μ (movingSampleTier (rep c).val.2)) (e i)
    ‖∑ x, movingOriginalPatternWeight e μ ν prime n pattern G x *
      movingPatternFlagProduct e prime n t small (movingPatternBulkLeaves n m slot perm) pattern rep x‖ ≤
      ((2 : ℝ) ^ Fintype.card C * E ^ (4 * n * 2 ^ n - Fintype.card C)) *
        ∑ x, productPrior law x * D x := by
  intro law
  let κ := (2 : ℝ) ^ Fintype.card C * E ^ (4 * n * 2 ^ n - Fintype.card C)
  have hκ : 0 ≤ κ := mul_nonneg (by positivity) (pow_nonneg hE _)
  have hlaw (i : Fin (N + 1)) (a : A) : 0 ≤ law i a := by
    dsimp only [law]
    cases e i with
    | inl b => exact hν b a
    | inr c => exact hμ _ a
  rw [movingPattern_original_bulk_mean_eq e μ ν prime hnmass t small slot perm pattern rep G seed]
  calc
    _ ≤ ∑ x, (D x * κ) * productPrior law x := norm_sum_le_of_le _ (fun x _ =>
      (movingPattern_flagged_pointwise_bound e μ ν prime n t small
        (movingPatternBulkLeaves n m slot perm) pattern rep E hprime hμ hν hbound
        (movingPatternBulkMean e ν slot G) x).trans
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hG x) hκ)
          (productPrior_nonneg law hlaw x)))
    _ = κ * ∑ x, productPrior law x * D x := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      ring

end Ostmann

end OAI
