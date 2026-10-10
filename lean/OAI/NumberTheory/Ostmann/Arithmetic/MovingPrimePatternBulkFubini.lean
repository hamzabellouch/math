import OAI.NumberTheory.Ostmann.Arithmetic.MovingPrimePatternFrozenMultiplier
import OAI.NumberTheory.Ostmann.Arithmetic.MovingPatternBulkFubini

namespace OAI

/-! # Original bulk law for the two-prime symbolic factors -/

namespace Ostmann
open scoped Classical BigOperators

noncomputable def movingPrimePatternBulkMultiplier {A B C : Type*} [Fintype A] [Fintype C] {N : ℕ}
    (e : Fin (N + 1) ≃ B ⊕ C) (μ : ℕ → A → ℝ) (prime : A → ℕ)
    (n : ℕ) (t : Bool → FrequencyTree ℤ n) (small bulk : Bool → TreeLeafTuple (List B) n)
    (pattern : Bool × MovingSampleIndex n → C)
    (rep : ∀ c, {i : Bool × MovingSampleIndex n // pattern i = c})
    (x : Fin (N + 1) → A) : ℂ :=
  (movingPairCompensatedMass μ prime ((movingSamplePairCoordinates A n).symm
    (fun i => x (e.symm (.inr (pattern i))))) : ℂ) *
    movingPatternPrimeFlagProduct e prime n t small bulk pattern rep x

theorem movingPrimePatternBulkMultiplier_frozen {A B C : Type*} [Fintype A] [Fintype C] {N n m : ℕ}
    (e : Fin (N + 1) ≃ B ⊕ C) (μ : ℕ → A → ℝ) (prime : A → ℕ)
    (t : Bool → FrequencyTree ℤ n) (small : Bool → TreeLeafTuple (List B) n)
    (slot : (TreeLeafIndex n × Fin m) ↪ B) (perm : Equiv.Perm (TreeLeafIndex n × Fin m))
    (pattern : Bool × MovingSampleIndex n → C)
    (rep : ∀ c, {i : Bool × MovingSampleIndex n // pattern i = c})
    (x y : TreeLeafIndex n × Fin m → A)
    (a : {i : Fin (N + 1) // i ∉ Set.range (movingPatternBulkEmbedding e slot)} → A) :
    movingPrimePatternBulkMultiplier e μ prime n t small (movingPatternBulkLeaves n m slot perm) pattern rep
        (joinBulkNonbulk (movingPatternBulkEmbedding e slot) x a) =
      movingPrimePatternBulkMultiplier e μ prime n t small (movingPatternBulkLeaves n m slot perm) pattern rep
        (joinBulkNonbulk (movingPatternBulkEmbedding e slot) y a) := by
  unfold movingPrimePatternBulkMultiplier
  rw [movingPairCompensatedMass_bulk_frozen e μ prime slot pattern x y a,
    movingPatternPrimeFlagProduct_bulk_frozen e prime t small slot perm pattern rep x y a]

theorem movingPrimePattern_original_bulk_fubini {A B C : Type*}
    [Fintype A] [Fintype B] [Fintype C] {N n m : ℕ}
    (e : Fin (N + 1) ≃ B ⊕ C) (μ : ℕ → A → ℝ) (ν : B → A → ℝ) (prime : A → ℕ)
    (t : Bool → FrequencyTree ℤ n) (small : Bool → TreeLeafTuple (List B) n)
    (slot : (TreeLeafIndex n × Fin m) ↪ B) (perm : Equiv.Perm (TreeLeafIndex n × Fin m))
    (pattern : Bool × MovingSampleIndex n → C)
    (rep : ∀ c, {i : Bool × MovingSampleIndex n // pattern i = c})
    (G : (Fin (N + 1) → A) → ℂ) (seed : TreeLeafIndex n × Fin m → A) :
    let bulk := movingPatternBulkLeaves n m slot perm
    let lift := movingPatternBulkEmbedding e slot
    let law := movingPatternExternalLaw e ν
    (∑ x, movingOriginalPatternWeight e μ ν prime n pattern G x *
      movingPatternPrimeFlagProduct e prime n t small bulk pattern rep x) =
      ∑ a : {i : Fin (N + 1) // i ∉ Set.range lift} → A,
        ((∏ i : {i : Fin (N + 1) // i ∉ Set.range lift}, law i (a i) : ℝ) : ℂ) *
          (movingPrimePatternBulkMultiplier e μ prime n t small bulk pattern rep (joinBulkNonbulk lift seed a) *
            ∑ x : TreeLeafIndex n × Fin m → A,
              ((∏ j, ν (slot j) (x j) : ℝ) : ℂ) *
                movingPatternInjectionGuard e G (joinBulkNonbulk lift x a)) := by
  dsimp only
  let lift := movingPatternBulkEmbedding e slot
  let law := movingPatternExternalLaw e ν
  let bulk := movingPatternBulkLeaves n m slot perm
  let M := movingPrimePatternBulkMultiplier e μ prime n t small bulk pattern rep
  have heq : (∑ x, movingOriginalPatternWeight e μ ν prime n pattern G x *
      movingPatternPrimeFlagProduct e prime n t small bulk pattern rep x) =
      ∑ x, ((∏ i, law i (x i) : ℝ) : ℂ) * (M x * movingPatternInjectionGuard e G x) := by
    apply Finset.sum_congr rfl
    intro x _
    rw [show (∏ i, law i (x i)) = ∏ b, ν b (x (e.symm (.inl b))) from
      movingPatternExternalLaw_product e ν x]
    unfold movingOriginalPatternWeight M movingPrimePatternBulkMultiplier
    ring
  rw [heq]
  have hsplit := finite_prior_selected_fubini lift law
    (fun x => M x * movingPatternInjectionGuard e G x)
  simp only [finite_univ_canonical] at hsplit ⊢
  rw [hsplit]
  apply Finset.sum_congr rfl
  intro a _
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  have hm := movingPrimePatternBulkMultiplier_frozen e μ prime t small slot perm pattern rep x seed a
  change M (joinBulkNonbulk lift x a) = M (joinBulkNonbulk lift seed a) at hm
  rw [hm]
  have hlaw (j : TreeLeafIndex n × Fin m) : law (lift j) (x j) = ν (slot j) (x j) := by
    change Sum.elim ν (fun _ _ => 1) (e (e.symm (.inl (slot j)))) (x j) = _
    rw [Equiv.apply_symm_apply]
    rfl
  simp only [hlaw]
  ring

end Ostmann

end OAI
