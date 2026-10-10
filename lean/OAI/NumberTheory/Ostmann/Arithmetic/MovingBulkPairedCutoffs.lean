import OAI.NumberTheory.Ostmann.Arithmetic.MovingBulkOriginalCoefficient
import OAI.NumberTheory.Ostmann.Arithmetic.MovingBulkLogFactors
import OAI.NumberTheory.Ostmann.Construction.ScheduledTreeBulkCoordinates
import OAI.NumberTheory.Ostmann.Characters.TreeTupleProfiles
import OAI.NumberTheory.Ostmann.Arithmetic.MovingPatternBulkBudgets

namespace OAI

/-! # Actual bulk leaf lists and their retained logarithmic cutoffs -/

namespace Ostmann
open scoped Classical BigOperators

theorem treeLeafProduct_eq_prod {A : Type*} [CommMonoid A] (n : ℕ)
    (a : TreeLeafTuple A n) :
    treeLeafProduct n a = ∏ i : TreeLeafIndex n, treeLeafTupleEquiv A n a i := by
  induction n with
  | zero =>
    change A at a
    change a = @Finset.prod Unit A _ Finset.univ (fun _ => a)
    simp
  | succ n ih =>
    change treeLeafProduct n a.1 * treeLeafProduct n a.2 =
      ∏ i : TreeLeafIndex n ⊕ TreeLeafIndex n,
        Sum.elim (treeLeafTupleEquiv A n a.1) (treeLeafTupleEquiv A n a.2) i
    rw [Fintype.prod_sum_type, ih, ih]
    rfl

noncomputable def movingBulkPairedCutoffSlots {B : Type*} (n : ℕ)
    (bulk : Bool → TreeLeafTuple (List B) n) : Fin (2 ^ n + 2 ^ n) → List B :=
  Fin.append (fun i => treeLeafTupleEquiv (List B) n (bulk false) ((treeLeafEnumeration n).symm i))
    (fun i => treeLeafTupleEquiv (List B) n (bulk true) ((treeLeafEnumeration n).symm i))

theorem movingBulkPairedCutoffSlots_product {B : Type*} (n : ℕ)
    (bulk : Bool → TreeLeafTuple (List B) n) (f : List B → ℝ) :
    (∏ j, f (movingBulkPairedCutoffSlots n bulk j)) =
      treeLeafProduct n (treeLeafMap f n (bulk false)) *
        treeLeafProduct n (treeLeafMap f n (bulk true)) := by
  simp only [movingBulkPairedCutoffSlots, Fin.prod_univ_add, Fin.append_left, Fin.append_right,
    treeLeafProduct_eq_prod, treeLeafTupleEquiv_map]
  exact congrArg₂ (· * ·)
    ((treeLeafEnumeration n).symm.prod_comp (fun i => f (treeLeafTupleEquiv (List B) n (bulk false) i)))
    ((treeLeafEnumeration n).symm.prod_comp (fun i => f (treeLeafTupleEquiv (List B) n (bulk true) i)))

theorem movingBulkPairedCutoffSlots_map {B C : Type*} (n : ℕ)
    (bulk : Bool → TreeLeafTuple (List B) n) (g : B → C) (j : Fin (2 ^ n + 2 ^ n)) :
    movingBulkPairedCutoffSlots n (fun b => treeLeafMap (List.map g) n (bulk b)) j =
      (movingBulkPairedCutoffSlots n bulk j).map g := by
  refine Fin.addCases ?_ ?_ j <;> intro i <;>
    simp only [movingBulkPairedCutoffSlots, Fin.append_left, Fin.append_right, treeLeafTupleEquiv_map]

theorem bulkLogCutoffWeight_map {B C : Type*} (value : C → ℝ)
    (g : B → C) (cb : ℝ) (slots : List B) :
    bulkLogCutoffWeight value cb (slots.map g) =
      bulkLogCutoffWeight (value ∘ g) cb slots := by
  simp only [bulkLogCutoffWeight, realSlotProduct, List.map_map]

theorem treeLeafTuple_list_length {B : Type*} (n : ℕ) (bulk : TreeLeafTuple (List B) n)
    (m : ℕ) (h : MovingLeafLengthLE n bulk m) (j : TreeLeafIndex n) :
    (treeLeafTupleEquiv (List B) n bulk j).length ≤ m := by
  induction n with
  | zero => exact h
  | succ n ih =>
    cases j with
    | inl j => exact ih bulk.1 h.1 j
    | inr j => exact ih bulk.2 h.2 j

theorem movingBulkPairedCutoffSlots_length {B : Type*} (n m : ℕ)
    (bulk : Bool → TreeLeafTuple (List B) n)
    (h : ∀ b, MovingLeafLengthLE n (bulk b) m) (j : Fin (2 ^ n + 2 ^ n)) :
    (movingBulkPairedCutoffSlots n bulk j).length ≤ m := by
  refine Fin.addCases ?_ ?_ j <;> intro i
  · simp only [movingBulkPairedCutoffSlots, Fin.append_left]
    exact treeLeafTuple_list_length n (bulk false) m (h false) _
  · simp only [movingBulkPairedCutoffSlots, Fin.append_right]
    exact treeLeafTuple_list_length n (bulk true) m (h true) _

end Ostmann

end OAI
