import OAI.NumberTheory.Ostmann.Arithmetic.MovingPatternArithmeticComparison
import OAI.NumberTheory.Ostmann.Arithmetic.MovingPatternBulkFrozen
import OAI.NumberTheory.Ostmann.Construction.SelectedPrimeFubini

namespace OAI

/-! # Symbolic internal factors are constant under selected bulk resampling -/

namespace Ostmann
open scoped Classical BigOperators

def movingPatternFeasible {B C : Type*} {N : ℕ} (e : Fin (N + 1) ≃ B ⊕ C)
    (n : ℕ) (t : Bool → FrequencyTree ℤ n) (small bulk : Bool → TreeLeafTuple (List B) n)
    (pattern : Bool × MovingSampleIndex n → C)
    (rep : ∀ c, {i : Bool × MovingSampleIndex n // pattern i = c}) : Prop :=
  let T := movingPatternFinData e n t small bulk pattern
  let base := movingPatternFinRepresentative e n t small bulk pattern rep
  ∀ c, lineFeasibleFlags true (fun s => arithmeticTestFlag (lineTestPolynomials
    (movingIndexedLine T (e.symm (.inr c)) (base c)) ⟨(base c).1, (base c).2.val⟩ s = 0))

/-- The only value-dependent part of the symbolic factor is one reciprocal
prime per class. All feasibility decisions are formal polynomial identities. -/
theorem movingPatternFlagProduct_eq {A B C : Type*} [Fintype C] {N : ℕ}
    (e : Fin (N + 1) ≃ B ⊕ C) (prime : A → ℕ)
    (n : ℕ) (t : Bool → FrequencyTree ℤ n) (small bulk : Bool → TreeLeafTuple (List B) n)
    (pattern : Bool × MovingSampleIndex n → C)
    (rep : ∀ c, {i : Bool × MovingSampleIndex n // pattern i = c}) (x : Fin (N + 1) → A) :
    movingPatternFlagProduct e prime n t small bulk pattern rep x =
      if movingPatternFeasible e n t small bulk pattern rep then
        ∏ c : C, ((prime (x (e.symm (.inr c))) : ℝ)⁻¹ : ℂ) else 0 := by
  by_cases h : movingPatternFeasible e n t small bulk pattern rep
  · rw [ite_eq_left h]
    unfold movingPatternFlagProduct
    apply Finset.prod_congr rfl
    intro c _
    simp only [internalLineFlagWeight, h c, ite_true, internalLineScalar, Complex.ofReal_inv]
  · rw [ite_eq_right h]
    obtain ⟨c, hc⟩ := not_forall.mp h
    unfold movingPatternFlagProduct
    apply Finset.prod_eq_zero (Finset.mem_univ c)
    simp only [internalLineFlagWeight, hc, ite_false, Complex.ofReal_zero]

theorem movingPatternFlagProduct_congr {A B C : Type*} [Fintype C] {N : ℕ}
    (e : Fin (N + 1) ≃ B ⊕ C) (prime : A → ℕ)
    (n : ℕ) (t : Bool → FrequencyTree ℤ n) (small bulk : Bool → TreeLeafTuple (List B) n)
    (pattern : Bool × MovingSampleIndex n → C)
    (rep : ∀ c, {i : Bool × MovingSampleIndex n // pattern i = c})
    (x y : Fin (N + 1) → A) (h : ∀ c, x (e.symm (.inr c)) = y (e.symm (.inr c))) :
    movingPatternFlagProduct e prime n t small bulk pattern rep x =
      movingPatternFlagProduct e prime n t small bulk pattern rep y := by
  rw [movingPatternFlagProduct_eq, movingPatternFlagProduct_eq]
  simp only [h]

/-- In the exact Fubini decomposition of the original law, these factors
belong wholly to the fixed nonbulk coefficient. -/
theorem movingPatternFlagProduct_bulk_frozen {A B C : Type*} [Fintype C] {N n m : ℕ}
    (e : Fin (N + 1) ≃ B ⊕ C) (prime : A → ℕ)
    (t : Bool → FrequencyTree ℤ n) (small : Bool → TreeLeafTuple (List B) n)
    (slot : (TreeLeafIndex n × Fin m) ↪ B) (perm : Equiv.Perm (TreeLeafIndex n × Fin m))
    (pattern : Bool × MovingSampleIndex n → C)
    (rep : ∀ c, {i : Bool × MovingSampleIndex n // pattern i = c})
    (x y : TreeLeafIndex n × Fin m → A)
    (a : {i : Fin (N + 1) // i ∉ Set.range (movingPatternBulkEmbedding e slot)} → A) :
    movingPatternFlagProduct e prime n t small (movingPatternBulkLeaves n m slot perm) pattern rep
        (joinBulkNonbulk (movingPatternBulkEmbedding e slot) x a) =
      movingPatternFlagProduct e prime n t small (movingPatternBulkLeaves n m slot perm) pattern rep
        (joinBulkNonbulk (movingPatternBulkEmbedding e slot) y a) := by
  apply movingPatternFlagProduct_congr
  intro c
  exact (joinBulkNonbulk_nonbulk _ x a
    ⟨e.symm (.inr c), movingPatternBulkEmbedding_internal_absent e slot c⟩).trans
      (joinBulkNonbulk_nonbulk _ y a
        ⟨e.symm (.inr c), movingPatternBulkEmbedding_internal_absent e slot c⟩).symm

theorem movingPairCompensatedMass_bulk_frozen {A B C : Type*} [Fintype A] {N n m : ℕ}
    (e : Fin (N + 1) ≃ B ⊕ C) (μ : ℕ → A → ℝ) (prime : A → ℕ)
    (slot : (TreeLeafIndex n × Fin m) ↪ B) (pattern : Bool × MovingSampleIndex n → C)
    (x y : TreeLeafIndex n × Fin m → A)
    (a : {i : Fin (N + 1) // i ∉ Set.range (movingPatternBulkEmbedding e slot)} → A) :
    movingPairCompensatedMass μ prime ((movingSamplePairCoordinates A n).symm
      (fun i => joinBulkNonbulk (movingPatternBulkEmbedding e slot) x a (e.symm (.inr (pattern i))))) =
    movingPairCompensatedMass μ prime ((movingSamplePairCoordinates A n).symm
      (fun i => joinBulkNonbulk (movingPatternBulkEmbedding e slot) y a (e.symm (.inr (pattern i))))) := by
  congr 2
  funext i
  exact (joinBulkNonbulk_nonbulk _ x a
    ⟨e.symm (.inr (pattern i)), movingPatternBulkEmbedding_internal_absent e slot (pattern i)⟩).trans
      (joinBulkNonbulk_nonbulk _ y a
        ⟨e.symm (.inr (pattern i)), movingPatternBulkEmbedding_internal_absent e slot (pattern i)⟩).symm

end Ostmann

end OAI
