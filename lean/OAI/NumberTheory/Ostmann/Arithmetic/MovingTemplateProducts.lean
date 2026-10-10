import OAI.NumberTheory.Ostmann.Arithmetic.MovingTemplateLeaves
import OAI.NumberTheory.Ostmann.Arithmetic.NodeBulkProducts

namespace OAI

/-! # Exact moduli of the regular-slot templates -/

namespace Ostmann
open scoped Classical BigOperators

theorem naturalProduct_bulkSlotLeaves {A : Type*} (value : A → ℕ) (n m : ℕ)
    (slot : TreeLeafIndex n × Fin m → A) :
    MovingSlotReversal.naturalProduct value (flattenMovingSlots n (bulkSlotLeaves n m slot)) =
      ∏ i, value (slot i) := by
  rw [movingSlotValues_flatten]
  have h : movingSlotValues value n (bulkSlotLeaves n m slot) =
      (treeLeafTupleEquiv ℕ n).symm (fun j => ∏ i : Fin m, value (slot (j, i))) := by
    apply (treeLeafTupleEquiv ℕ n).injective
    funext j
    rw [movingSlotValues_indexed, Equiv.apply_symm_apply]
    simp only [bulkSlotLeaves, Equiv.apply_symm_apply, MovingSlotReversal.naturalProduct,
      List.map_ofFn, List.prod_ofFn]
    rfl
  rw [h, treeLeafProduct_indexed, Fintype.prod_prod_type]

/-- Every regular coordinate occurs once in the small/bulk leaf lists. -/
theorem movingTemplate_product {A : Type*} (value : A → ℕ) (n r m : ℕ)
    (y : MovingRegularSlot n r m → A) :
    MovingSlotReversal.naturalProduct (value ∘ y)
      (flattenMovingSlots n (movingTemplateSmall n r m) ++
        flattenMovingSlots n (bulkSlotLeaves n m (movingTemplateBulk n r m))) =
      ∏ i, value (y i) := by
  rw [movingNaturalProduct_append]
  unfold movingTemplateSmall
  rw [naturalProduct_bulkSlotLeaves, naturalProduct_bulkSlotLeaves]
  simp only [MovingRegularSlot, Fintype.prod_prod_type, Fintype.prod_sum_type,
    Function.comp_apply, movingTemplateBulk]
  rw [Finset.prod_mul_distrib]
  rfl

/-- The extracted compensation modulus is exactly the factor removed from
one child's complete regular modulus. -/
theorem movingRestoreSample_product {A : Type*} (value : A → ℕ) (n r m : ℕ)
    (u : TreeLeafIndex n × Fin 4 → A) (y : MovingRegularSlot n r m → A) :
    (∏ i, value (movingRestoreSample n r m u y i)) =
      (∏ i, value (u i)) * ∏ i, value (y i) := by
  have h := (movingReverseTemplate n r m).prod_comp
    (fun i => value (movingRestoreSample n r m u y i))
  rw [Fintype.prod_sum_type] at h
  simpa only [movingRestoreSample, Function.comp_apply, Equiv.symm_apply_apply,
    Sum.elim_inl, Sum.elim_inr] using h.symm

end Ostmann

end OAI
