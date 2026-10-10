import OAI.NumberTheory.Ostmann.Arithmetic.MovingPatternArithmeticData

namespace OAI

/-! # The common regular product under an arbitrary bulk matching -/

namespace Ostmann
open scoped Classical

theorem bulkSlotLeaves_perm_matching {σ : Type*} (n m : ℕ)
    (slot : (TreeLeafIndex n × Fin m) ↪ σ)
    (perm : Equiv.Perm (TreeLeafIndex n × Fin m)) :
    (flattenMovingSlots n (bulkSlotLeaves n m (slot ∘ perm.symm))).Perm
      (flattenMovingSlots n (bulkSlotLeaves n m slot)) := by
  apply (List.perm_ext_iff_of_nodup
    (bulkSlotLeaves_nodup n m _ (slot.injective.comp perm.symm.injective))
    (bulkSlotLeaves_nodup n m slot slot.injective)).mpr
  intro i
  rw [mem_flatten_bulkSlotLeaves, mem_flatten_bulkSlotLeaves]
  constructor
  · rintro ⟨j, hj⟩
    exact ⟨perm.symm j, hj⟩
  · rintro ⟨j, hj⟩
    refine ⟨perm j, ?_⟩
    simpa only [Function.comp_apply, Equiv.symm_apply_apply] using hj

/-- A matching changes only the distribution of the bulk labels among leaves.
The regular product of the complete tree is preserved, even when the sampled
prime values have collisions. -/
theorem movingPatternFinBulkData_regular_product_permuted {B C : Type*} {N n m : ℕ}
    (e : Fin (N + 1) ≃ B ⊕ C) (t : Bool → FrequencyTree ℤ n)
    (small : TreeLeafTuple (List B) n) (slot : (TreeLeafIndex n × Fin m) ↪ B)
    (perm : Equiv.Perm (TreeLeafIndex n × Fin m))
    (pattern : Bool × MovingSampleIndex n → C) (value : Fin (N + 1) → ℕ) (b : Bool) :
    MovingSlotReversal.naturalProduct value
      (movingPatternFinBulkData e n m t (fun _ => small) slot perm pattern b).regularSlots =
    MovingSlotReversal.naturalProduct value
      (flattenMovingSlots n (movingPatternFiniteSmall e n small) ++
        flattenMovingSlots n (bulkSlotLeaves n m (movingPatternBulkEmbedding e slot))) := by
  rw [movingPatternFinBulkData_build]
  let bulk := if b then bulkSlotLeaves n m (movingPatternBulkEmbedding e slot ∘ perm.symm)
    else bulkSlotLeaves n m (movingPatternBulkEmbedding e slot)
  have hp := buildMovingSlotData_regular_perm n (t b)
    (movingPatternFiniteSmall e n small) bulk (movingPatternFiniteSamples e n pattern b)
  have hb : (flattenMovingSlots n bulk).Perm
      (flattenMovingSlots n (bulkSlotLeaves n m (movingPatternBulkEmbedding e slot))) := by
    cases b
    · exact List.Perm.refl _
    · exact bulkSlotLeaves_perm_matching n m (movingPatternBulkEmbedding e slot) perm
  exact ((hp.trans ((List.Perm.refl _).append hb)).map value).prod_eq

end Ostmann

end OAI
