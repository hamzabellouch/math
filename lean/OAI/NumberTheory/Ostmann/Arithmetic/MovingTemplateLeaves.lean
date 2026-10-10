import OAI.NumberTheory.Ostmann.Arithmetic.MovingTemplatePrior
import OAI.NumberTheory.Ostmann.Arithmetic.MovingPatternBulkData

namespace OAI

/-! # Restoring the four compensation primes in each actual leaf -/

namespace Ostmann
open scoped Classical BigOperators

theorem treeLeafTupleEquiv_append_slots {A : Type*} (n : ℕ)
    (x y : TreeLeafTuple (List A) n) (j : TreeLeafIndex n) :
    treeLeafTupleEquiv (List A) n (appendMovingSlotLeaves n x y) j =
      treeLeafTupleEquiv (List A) n x j ++ treeLeafTupleEquiv (List A) n y j := by
  induction n with
  | zero => rfl
  | succ n ih => cases j with
    | inl j => exact ih x.1 y.1 j
    | inr j => exact ih x.2 y.2 j

theorem treeLeafTupleEquiv_compensation_slots {A : Type*} (n : ℕ)
    (a : TreeLeafTuple (Fin 4 → A) n) (j : TreeLeafIndex n) :
    treeLeafTupleEquiv (List A) n (movingCompensationSlots n a) j =
      List.ofFn (treeLeafTupleEquiv (Fin 4 → A) n a j) := by
  induction n with
  | zero => rfl
  | succ n ih => cases j with
    | inl j => exact ih a.1 j
    | inr j => exact ih a.2 j

/-- Restoring the same compensation sample in every surviving leaf gives
exactly the small list required by the two child recursions. -/
theorem movingRestoreSample_small_leaves {A : Type*} (n r m : ℕ)
    (u : TreeLeafIndex n × Fin 4 → A) (y : MovingRegularSlot n r m → A) :
    treeLeafMap (List.map (movingRestoreSample n r m u y)) n (movingTemplateSmall n (4 + r) m) =
      appendMovingSlotLeaves n
        (movingCompensationSlots n ((treeLeafTupleEquiv (Fin 4 → A) n).symm
          (fun j i => u (j, i))))
        (treeLeafMap (List.map y) n (movingTemplateSmall n r m)) := by
  apply (treeLeafTupleEquiv (List A) n).injective
  funext j
  rw [treeLeafTupleEquiv_map, treeLeafTupleEquiv_append_slots,
    treeLeafTupleEquiv_compensation_slots, Equiv.apply_symm_apply,
    treeLeafTupleEquiv_map]
  simp only [movingTemplateSmall, bulkSlotLeaves, Equiv.apply_symm_apply, List.map_ofFn]
  rw [List.ofFn_add]
  change (List.ofFn (fun i : Fin 4 =>
      movingRestoreSample n r m u y (j, .inl (Fin.castAdd r i)))) ++
    (List.ofFn (fun i : Fin r =>
      movingRestoreSample n r m u y (j, .inl (Fin.natAdd 4 i)))) = _
  simp only [movingRestoreSample_small]
  rfl

theorem movingRestoreSample_bulk_leaves {A : Type*} (n r m : ℕ)
    (u : TreeLeafIndex n × Fin 4 → A) (y : MovingRegularSlot n r m → A) :
    treeLeafMap (List.map (movingRestoreSample n r m u y)) n
        (bulkSlotLeaves n m (movingTemplateBulk n (4 + r) m)) =
      treeLeafMap (List.map y) n (bulkSlotLeaves n m (movingTemplateBulk n r m)) := by
  rw [bulkSlotLeaves_map, bulkSlotLeaves_map]
  congr 1

end Ostmann

end OAI
