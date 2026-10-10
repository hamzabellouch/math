import OAI.NumberTheory.Ostmann.Arithmetic.MovingPatternBulkData
import OAI.NumberTheory.Ostmann.Arithmetic.MovingCompensationSupport

namespace OAI

/-! # Arithmetic support of the actual finite pattern trees -/

namespace Ostmann
open scoped Classical

theorem movingPatternFinBulkData_regular_coherent {B C : Type*} {N n m : ℕ}
    (e : Fin (N + 1) ≃ B ⊕ C) (t : Bool → FrequencyTree ℤ n)
    (small : Bool → TreeLeafTuple (List B) n) (slot : (TreeLeafIndex n × Fin m) ↪ B)
    (perm : Equiv.Perm (TreeLeafIndex n × Fin m)) (pattern : Bool × MovingSampleIndex n → C)
    (b : Bool) : (movingPatternFinBulkData e n m t small slot perm pattern b).RegularCoherent := by
  rw [movingPatternFinBulkData_build]
  exact buildMovingSlotData_regular_coherent _ _ _ _ _

/-- Every compensation prime comes from an internal equality class. The
strict level separation excludes all external regular slots. -/
theorem movingPatternFinBulkData_internal_cover {A B C : Type*} [Fintype C] {N n m : ℕ}
    (e : Fin (N + 1) ≃ B ⊕ C) (tierB : B → ℕ) (tierC : C → ℕ)
    (t : Bool → FrequencyTree ℤ n) (small : Bool → TreeLeafTuple (List B) n)
    (slot : (TreeLeafIndex n × Fin m) ↪ B) (perm : Equiv.Perm (TreeLeafIndex n × Fin m))
    (pattern : Bool × MovingSampleIndex n → C)
    (hB : ∀ j, n ≤ tierB j) (htier : ∀ i, tierC (pattern i) = movingSampleTier i.2)
    (value : A → ℕ) (x : Fin (N + 1) → A) :
    ∀ b, ∀ o ∈ (movingPatternFinBulkData e n m t small slot perm pattern b).occurrences,
      ∀ i ∈ o.current.compensationSlots,
        value (x i) ∈ Finset.univ.image (fun c : C => value (x (e.symm (.inr c)))) := by
  intro b o ho i hi
  let tier := (Sum.elim tierB tierC) ∘ e
  let T := movingPatternFinBulkData e n m t small slot perm pattern b
  have hlevels : T.Levels tier :=
    movingPatternFinBulkData_levels e tierB tierC n m t small slot perm pattern hB htier b
  have hlt := T.occurrence_compensation_level tier hlevels o ho i hi
  have hbound := (T.occurrence_bounds tier hlevels o ho).2.1
  have hiN : tier i < n := lt_of_lt_of_le hlt (by omega)
  cases he : e i with
  | inl j =>
    have hj := hB j
    simp only [tier, Function.comp_apply, he, Sum.elim_inl] at hiN
    omega
  | inr c =>
    apply Finset.mem_image.mpr
    refine ⟨c, Finset.mem_univ _, ?_⟩
    have hh := e.symm_apply_apply i
    rw [he] at hh
    rw [hh]

/-- Both histories have the same top regular product. No sampled internal
prime or history frequency enters this product. -/
theorem movingPatternFinBulkData_regular_product {B C : Type*} {N n m : ℕ}
    (e : Fin (N + 1) ≃ B ⊕ C) (t : Bool → FrequencyTree ℤ n)
    (small : TreeLeafTuple (List B) n) (slot : (TreeLeafIndex n × Fin m) ↪ B)
    (pattern : Bool × MovingSampleIndex n → C) (value : Fin (N + 1) → ℕ) (b : Bool) :
    MovingSlotReversal.naturalProduct value
      (movingPatternFinBulkData e n m t (fun _ => small) slot (Equiv.refl _) pattern b).regularSlots =
    MovingSlotReversal.naturalProduct value
      (flattenMovingSlots n (movingPatternFiniteSmall e n small) ++
        flattenMovingSlots n (bulkSlotLeaves n m (movingPatternBulkEmbedding e slot))) := by
  rw [movingPatternFinBulkData_build]
  have hp := buildMovingSlotData_regular_perm n (t b)
    (movingPatternFiniteSmall e n small)
    (bulkSlotLeaves n m (movingPatternBulkEmbedding e slot))
    (movingPatternFiniteSamples e n pattern b)
  have he : (if b then bulkSlotLeaves n m (movingPatternBulkEmbedding e slot ∘ (Equiv.refl _).symm)
      else bulkSlotLeaves n m (movingPatternBulkEmbedding e slot)) =
      bulkSlotLeaves n m (movingPatternBulkEmbedding e slot) := by cases b <;> rfl
  rw [he]
  exact (hp.map value).prod_eq

end Ostmann

end OAI
