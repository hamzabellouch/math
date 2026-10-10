import OAI.NumberTheory.Ostmann.Arithmetic.MovingPatternFinite
import OAI.NumberTheory.Ostmann.Arithmetic.BulkSlotNodup
import OAI.NumberTheory.Ostmann.Arithmetic.FrozenMovingSamples

namespace OAI

/-! # The original pattern pair in selected bulk coordinates -/

namespace Ostmann
open scoped Classical

theorem bulkSlotLeaves_map {A B : Type*} (f : A → B) (n m : ℕ)
    (slot : TreeLeafIndex n × Fin m → A) :
    treeLeafMap (List.map f) n (bulkSlotLeaves n m slot) =
      bulkSlotLeaves n m (f ∘ slot) := by
  apply (treeLeafTupleEquiv (List B) n).injective
  funext j
  rw [treeLeafTupleEquiv_map]
  simp only [bulkSlotLeaves, Equiv.apply_symm_apply, List.map_ofFn, Function.comp_def]

def movingPatternBulkEmbedding {B C : Type*} {N : ℕ} (e : Fin (N + 1) ≃ B ⊕ C)
    {n m : ℕ} (slot : (TreeLeafIndex n × Fin m) ↪ B) :
    (TreeLeafIndex n × Fin m) ↪ Fin (N + 1) where
  toFun j := e.symm (.inl (slot j))
  inj' := fun _ _ h => slot.injective (Sum.inl.inj (e.symm.injective h))

def movingPatternFiniteSmall {B C : Type*} {N : ℕ} (e : Fin (N + 1) ≃ B ⊕ C)
    (n : ℕ) (small : TreeLeafTuple (List B) n) : TreeLeafTuple (List (Fin (N + 1))) n :=
  treeLeafMap (List.map (fun b => e.symm (.inl b))) n small

def movingPatternFiniteSamples {B C : Type*} {N : ℕ} (e : Fin (N + 1) ≃ B ⊕ C)
    (n : ℕ) (pattern : Bool × MovingSampleIndex n → C) (side : Bool) :
    MovingSampleSlots (Fin (N + 1)) n :=
  movingPatternSamples (Fin (N + 1)) n ((fun c => e.symm (.inr c)) ∘ pattern) side

theorem movingPatternFinData_build {B C : Type*} {N : ℕ} (e : Fin (N + 1) ≃ B ⊕ C)
    (n : ℕ) (t : Bool → FrequencyTree ℤ n) (small bulk : Bool → TreeLeafTuple (List B) n)
    (pattern : Bool × MovingSampleIndex n → C) (side : Bool) :
    movingPatternFinData e n t small bulk pattern side =
      buildMovingSlotData n (t side) (movingPatternFiniteSmall e n (small side))
        (movingPatternFiniteSmall e n (bulk side))
        (movingPatternFiniteSamples e n pattern side) := by
  unfold movingPatternFinData movingPatternSlotData
  rw [buildMovingSlotData_map, treeLeafMap_list_comp, treeLeafMap_list_comp,
    movingPatternSamples_map]
  rfl

noncomputable def movingPatternBulkLeaves {B : Type*} (n m : ℕ)
    (slot : (TreeLeafIndex n × Fin m) ↪ B)
    (perm : Equiv.Perm (TreeLeafIndex n × Fin m)) (side : Bool) :
    TreeLeafTuple (List B) n :=
  if side then bulkSlotLeaves n m (slot ∘ perm.symm) else bulkSlotLeaves n m slot

noncomputable def movingPatternFinBulkData {B C : Type*} {N : ℕ} (e : Fin (N + 1) ≃ B ⊕ C)
    (n m : ℕ) (t : Bool → FrequencyTree ℤ n) (small : Bool → TreeLeafTuple (List B) n)
    (slot : (TreeLeafIndex n × Fin m) ↪ B)
    (perm : Equiv.Perm (TreeLeafIndex n × Fin m))
    (pattern : Bool × MovingSampleIndex n → C) (side : Bool) :
    MovingSlotData (Fin (N + 1)) n :=
  movingPatternFinData e n t small (movingPatternBulkLeaves n m slot perm) pattern side

theorem movingPatternFinBulkData_build {B C : Type*} {N : ℕ} (e : Fin (N + 1) ≃ B ⊕ C)
    (n m : ℕ) (t : Bool → FrequencyTree ℤ n) (small : Bool → TreeLeafTuple (List B) n)
    (slot : (TreeLeafIndex n × Fin m) ↪ B)
    (perm : Equiv.Perm (TreeLeafIndex n × Fin m))
    (pattern : Bool × MovingSampleIndex n → C) (side : Bool) :
    movingPatternFinBulkData e n m t small slot perm pattern side =
      buildMovingSlotData n (t side) (movingPatternFiniteSmall e n (small side))
        (if side then bulkSlotLeaves n m (movingPatternBulkEmbedding e slot ∘ perm.symm)
          else bulkSlotLeaves n m (movingPatternBulkEmbedding e slot))
        (movingPatternFiniteSamples e n pattern side) := by
  rw [movingPatternFinBulkData, movingPatternFinData_build]
  cases side <;>
    simp only [movingPatternFiniteSmall, movingPatternBulkLeaves, Bool.false_eq_true,
      ite_false, ite_true, bulkSlotLeaves_map]
  <;> rfl

theorem movingPatternFiniteSamples_levels {B C : Type*} {N : ℕ}
    (e : Fin (N + 1) ≃ B ⊕ C) (tierB : B → ℕ) (tierC : C → ℕ)
    (n : ℕ) (pattern : Bool × MovingSampleIndex n → C)
    (htier : ∀ i, tierC (pattern i) = movingSampleTier i.2) (side : Bool) :
    (movingPatternFiniteSamples e n pattern side).Levels ((Sum.elim tierB tierC) ∘ e) := by
  apply movingSampleCoordinates_levels
  intro i
  simpa only [Function.comp_apply, Equiv.apply_symm_apply, Sum.elim_inr] using htier (side, i)

theorem movingPatternFinBulkData_levels {B C : Type*} {N : ℕ}
    (e : Fin (N + 1) ≃ B ⊕ C) (tierB : B → ℕ) (tierC : C → ℕ)
    (n m : ℕ) (t : Bool → FrequencyTree ℤ n) (small : Bool → TreeLeafTuple (List B) n)
    (slot : (TreeLeafIndex n × Fin m) ↪ B)
    (perm : Equiv.Perm (TreeLeafIndex n × Fin m))
    (pattern : Bool × MovingSampleIndex n → C)
    (hB : ∀ i, n ≤ tierB i) (htier : ∀ i, tierC (pattern i) = movingSampleTier i.2)
    (side : Bool) :
    (movingPatternFinBulkData e n m t small slot perm pattern side).Levels
      ((Sum.elim tierB tierC) ∘ e) :=
  movingPatternFinData_levels e tierB tierC n t small _ pattern
    (fun _ i _ => hB i) (fun _ i _ => hB i) htier side

theorem movingPatternFinBulkData_compensationAbsent {B C : Type*} {N : ℕ}
    (e : Fin (N + 1) ≃ B ⊕ C) (tierB : B → ℕ) (tierC : C → ℕ)
    (n m : ℕ) (t : Bool → FrequencyTree ℤ n) (small : Bool → TreeLeafTuple (List B) n)
    (slot : (TreeLeafIndex n × Fin m) ↪ B)
    (perm : Equiv.Perm (TreeLeafIndex n × Fin m))
    (pattern : Bool × MovingSampleIndex n → C)
    (hB : ∀ i, n ≤ tierB i) (htier : ∀ i, tierC (pattern i) = movingSampleTier i.2)
    (side : Bool) (j : TreeLeafIndex n × Fin m) :
    (movingPatternFinBulkData e n m t small slot perm pattern side).CompensationAbsent
      (movingPatternBulkEmbedding e slot j) := by
  apply MovingSlotData.compensationAbsent_of_levels ((Sum.elim tierB tierC) ∘ e) _
    (movingPatternFinBulkData_levels e tierB tierC n m t small slot perm pattern hB htier side)
  change n ≤ Sum.elim tierB tierC (e (e.symm (.inl (slot j))))
  simpa only [Equiv.apply_symm_apply, Sum.elim_inl] using hB (slot j)

end Ostmann

end OAI
