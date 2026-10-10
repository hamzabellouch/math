import OAI.NumberTheory.Ostmann.Arithmetic.MovingPrimePatternBulkFubini
import OAI.NumberTheory.Ostmann.Arithmetic.MovingPrimePatternFlagBound
import OAI.NumberTheory.Ostmann.Arithmetic.MovingPatternBulkMean

namespace OAI

/-! # Original bulk law for the two-prime symbolic factors -/

namespace Ostmann
open scoped Classical BigOperators

private theorem movingPatternBulkMean_guard_average {A B C : Type*} [Fintype A] {N n m : ℕ}
    (e : Fin (N + 1) ≃ B ⊕ C) (ν : B → A → ℝ)
    (hmass : ∀ j, ∑ a, ν j a = 1) (slot : (TreeLeafIndex n × Fin m) ↪ B)
    (G : (Fin (N + 1) → A) → ℂ)
    (a : {i : Fin (N + 1) // i ∉ Set.range (movingPatternBulkEmbedding e slot)} → A) :
    (∑ z : TreeLeafIndex n × Fin m → A, ((∏ j, ν (slot j) (z j) : ℝ) : ℂ) *
      movingPatternInjectionGuard e (movingPatternBulkMean e ν slot G)
        (joinBulkNonbulk (movingPatternBulkEmbedding e slot) z a)) =
    ∑ z : TreeLeafIndex n × Fin m → A, ((∏ j, ν (slot j) (z j) : ℝ) : ℂ) *
      movingPatternInjectionGuard e G (joinBulkNonbulk (movingPatternBulkEmbedding e slot) z a) := by
  have hmR : (∑ z : TreeLeafIndex n × Fin m → A, ∏ j, ν (slot j) (z j)) = 1 := by
    rw [← Fintype.prod_sum]
    simp only [hmass, Finset.prod_const_one]
  have hm : (∑ z : TreeLeafIndex n × Fin m → A, ((∏ j, ν (slot j) (z j) : ℝ) : ℂ)) = 1 := by
    exact_mod_cast hmR
  simp_rw [movingPatternInjectionGuard_join, movingPatternBulkMean_join]
  by_cases h : Function.Injective
      (fun c => a ⟨e.symm (.inr c), movingPatternBulkEmbedding_internal_absent e slot c⟩)
  · simp only [h, ite_true]
    rw [← Finset.sum_mul, hm, one_mul]
  · simp only [h, ite_false, mul_zero, Finset.sum_const_zero]

/-- Averaging only selected bulk coordinates preserves the original signed
pattern expression, including the class-injectivity guard. -/
theorem movingPrimePattern_original_bulk_mean_eq {A B C : Type*}
    [Fintype A] [Fintype B] [Fintype C] {N n m : ℕ}
    (e : Fin (N + 1) ≃ B ⊕ C) (μ : ℕ → A → ℝ) (ν : B → A → ℝ) (prime : A → ℕ)
    (hmass : ∀ j, ∑ a, ν j a = 1)
    (t : Bool → FrequencyTree ℤ n) (small : Bool → TreeLeafTuple (List B) n)
    (slot : (TreeLeafIndex n × Fin m) ↪ B) (perm : Equiv.Perm (TreeLeafIndex n × Fin m))
    (pattern : Bool × MovingSampleIndex n → C)
    (rep : ∀ c, {i : Bool × MovingSampleIndex n // pattern i = c})
    (G : (Fin (N + 1) → A) → ℂ) (seed : TreeLeafIndex n × Fin m → A) :
    (∑ x, movingOriginalPatternWeight e μ ν prime n pattern G x *
      movingPatternPrimeFlagProduct e prime n t small (movingPatternBulkLeaves n m slot perm) pattern rep x) =
    ∑ x, movingOriginalPatternWeight e μ ν prime n pattern (movingPatternBulkMean e ν slot G) x *
      movingPatternPrimeFlagProduct e prime n t small (movingPatternBulkLeaves n m slot perm) pattern rep x := by
  rw [movingPrimePattern_original_bulk_fubini e μ ν prime t small slot perm pattern rep G seed,
    movingPrimePattern_original_bulk_fubini e μ ν prime t small slot perm pattern rep
      (movingPatternBulkMean e ν slot G) seed]
  apply Finset.sum_congr rfl
  intro a _
  rw [movingPatternBulkMean_guard_average e ν hmass slot G a]

/-- A bound proved for the actual signed bulk mean lifts to the full original
pattern law with only its depth-dependent representative-prior cost. -/
theorem movingPrimePattern_signed_bulk_mean_bound {A B C : Type*}
    [Fintype A] [Fintype B] [Fintype C] {N n m : ℕ}
    (e : Fin (N + 1) ≃ B ⊕ C) (μ : ℕ → A → ℝ) (ν : B → A → ℝ) (prime : A → ℕ)
    (t : Bool → FrequencyTree ℤ n) (small : Bool → TreeLeafTuple (List B) n)
    (slot : (TreeLeafIndex n × Fin m) ↪ B) (perm : Equiv.Perm (TreeLeafIndex n × Fin m))
    (pattern : Bool × MovingSampleIndex n → C)
    (rep : ∀ c, {i : Bool × MovingSampleIndex n // pattern i = c}) (E : ℝ)
    (hprime : ∀ a, (prime a).Prime) (hμ : ∀ j a, 0 ≤ μ j a) (hν : ∀ j a, 0 ≤ ν j a)
    (hmass : ∀ j, ∑ a, μ j a = 1) (hnmass : ∀ j, ∑ a, ν j a = 1)
    (hbound : ∀ j a, (prime a : ℝ) * μ j a ≤ E)
    (G : (Fin (N + 1) → A) → ℂ) (D : ℝ) (hD : 0 ≤ D)
    (hG : ∀ x, ‖movingPatternBulkMean e ν slot G x‖ ≤ D)
    (seed : TreeLeafIndex n × Fin m → A) :
    ‖∑ x, movingOriginalPatternWeight e μ ν prime n pattern G x *
        movingPatternPrimeFlagProduct e prime n t small (movingPatternBulkLeaves n m slot perm) pattern rep x‖ ≤
      D * ((4 : ℝ) ^ Fintype.card C * E ^ (4 * n * 2 ^ n - Fintype.card C)) := by
  rw [movingPrimePattern_original_bulk_mean_eq e μ ν prime hnmass t small slot perm pattern rep G seed]
  exact movingPrimePattern_flagged_mean_bound e μ ν prime n t small _ pattern rep E hprime hμ hν
    hmass hnmass hbound _ D hD hG

end Ostmann

end OAI
