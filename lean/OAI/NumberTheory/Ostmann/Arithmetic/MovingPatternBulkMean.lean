import OAI.NumberTheory.Ostmann.Arithmetic.MovingPatternBulkFubini
import OAI.NumberTheory.Ostmann.Arithmetic.MovingPatternFlagBound

namespace OAI

/-! # Lifting signed cancellation in the original bulk mean -/

namespace Ostmann
open scoped Classical BigOperators

noncomputable def movingPatternBulkMean {A B C : Type*} [Fintype A] {N n m : ℕ}
    (e : Fin (N + 1) ≃ B ⊕ C) (ν : B → A → ℝ)
    (slot : (TreeLeafIndex n × Fin m) ↪ B) (G : (Fin (N + 1) → A) → ℂ)
    (x : Fin (N + 1) → A) : ℂ :=
  ∑ z : TreeLeafIndex n × Fin m → A, ((∏ j, ν (slot j) (z j) : ℝ) : ℂ) *
    G (joinBulkNonbulk (movingPatternBulkEmbedding e slot) z (fun i => x i))

theorem movingPatternBulkMean_join {A B C : Type*} [Fintype A] {N n m : ℕ}
    (e : Fin (N + 1) ≃ B ⊕ C) (ν : B → A → ℝ)
    (slot : (TreeLeafIndex n × Fin m) ↪ B) (G : (Fin (N + 1) → A) → ℂ)
    (z : TreeLeafIndex n × Fin m → A)
    (a : {i : Fin (N + 1) // i ∉ Set.range (movingPatternBulkEmbedding e slot)} → A) :
    movingPatternBulkMean e ν slot G (joinBulkNonbulk (movingPatternBulkEmbedding e slot) z a) =
      ∑ w : TreeLeafIndex n × Fin m → A, ((∏ j, ν (slot j) (w j) : ℝ) : ℂ) *
        G (joinBulkNonbulk (movingPatternBulkEmbedding e slot) w a) := by
  have h : (fun i : {i : Fin (N + 1) // i ∉ Set.range (movingPatternBulkEmbedding e slot)} =>
      joinBulkNonbulk (movingPatternBulkEmbedding e slot) z a i) = a := by
    funext i
    exact joinBulkNonbulk_nonbulk _ z a i
  unfold movingPatternBulkMean
  rw [h]

theorem movingPatternInjectionGuard_join {A B C : Type*} {N n m : ℕ}
    (e : Fin (N + 1) ≃ B ⊕ C) (slot : (TreeLeafIndex n × Fin m) ↪ B)
    (G : (Fin (N + 1) → A) → ℂ) (z : TreeLeafIndex n × Fin m → A)
    (a : {i : Fin (N + 1) // i ∉ Set.range (movingPatternBulkEmbedding e slot)} → A) :
    movingPatternInjectionGuard e G (joinBulkNonbulk (movingPatternBulkEmbedding e slot) z a) =
      if Function.Injective (fun c => a ⟨e.symm (.inr c), movingPatternBulkEmbedding_internal_absent e slot c⟩)
      then G (joinBulkNonbulk (movingPatternBulkEmbedding e slot) z a) else 0 := by
  have h : (fun c => joinBulkNonbulk (movingPatternBulkEmbedding e slot) z a (e.symm (.inr c))) =
      (fun c => a ⟨e.symm (.inr c), movingPatternBulkEmbedding_internal_absent e slot c⟩) := by
    funext c
    exact joinBulkNonbulk_nonbulk _ z a
      ⟨e.symm (.inr c), movingPatternBulkEmbedding_internal_absent e slot c⟩
  unfold movingPatternInjectionGuard
  rw [h]

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
theorem movingPattern_original_bulk_mean_eq {A B C : Type*}
    [Fintype A] [Fintype B] [Fintype C] {N n m : ℕ}
    (e : Fin (N + 1) ≃ B ⊕ C) (μ : ℕ → A → ℝ) (ν : B → A → ℝ) (prime : A → ℕ)
    (hmass : ∀ j, ∑ a, ν j a = 1)
    (t : Bool → FrequencyTree ℤ n) (small : Bool → TreeLeafTuple (List B) n)
    (slot : (TreeLeafIndex n × Fin m) ↪ B) (perm : Equiv.Perm (TreeLeafIndex n × Fin m))
    (pattern : Bool × MovingSampleIndex n → C)
    (rep : ∀ c, {i : Bool × MovingSampleIndex n // pattern i = c})
    (G : (Fin (N + 1) → A) → ℂ) (seed : TreeLeafIndex n × Fin m → A) :
    (∑ x, movingOriginalPatternWeight e μ ν prime n pattern G x *
      movingPatternFlagProduct e prime n t small (movingPatternBulkLeaves n m slot perm) pattern rep x) =
    ∑ x, movingOriginalPatternWeight e μ ν prime n pattern (movingPatternBulkMean e ν slot G) x *
      movingPatternFlagProduct e prime n t small (movingPatternBulkLeaves n m slot perm) pattern rep x := by
  rw [movingPattern_original_bulk_fubini e μ ν prime t small slot perm pattern rep G seed,
    movingPattern_original_bulk_fubini e μ ν prime t small slot perm pattern rep
      (movingPatternBulkMean e ν slot G) seed]
  apply Finset.sum_congr rfl
  intro a _
  rw [movingPatternBulkMean_guard_average e ν hmass slot G a]

/-- A bound proved for the actual signed bulk mean lifts to the full original
pattern law with only its depth-dependent representative-prior cost. -/
theorem movingPattern_signed_bulk_mean_bound {A B C : Type*}
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
        movingPatternFlagProduct e prime n t small (movingPatternBulkLeaves n m slot perm) pattern rep x‖ ≤
      D * ((2 : ℝ) ^ Fintype.card C * E ^ (4 * n * 2 ^ n - Fintype.card C)) := by
  rw [movingPattern_original_bulk_mean_eq e μ ν prime hnmass t small slot perm pattern rep G seed]
  exact movingPattern_flagged_mean_bound e μ ν prime n t small _ pattern rep E hprime hμ hν
    hmass hnmass hbound _ D hD hG

end Ostmann

end OAI
