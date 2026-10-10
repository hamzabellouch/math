import OAI.Analysis.KadisonKastler.OrderedTuples
import OAI.Analysis.KadisonKastler.PreservationMatrix
import Mathlib.Logic.Equiv.Fin.Basic

namespace OAI

/-!
# Splitting distinct ordered words at a cut

Concatenation identifies injective ordered words with pairs of injective
subwords having disjoint underlying subsets. At a preservation cut the
unique omitted label is recovered from the complementary singleton.
-/

namespace KadisonKastler

open Finset
open scoped BigOperators

noncomputable section

variable {α : Type*} [Fintype α] [DecidableEq α]

abbrev DisjointOrderedTuplePair (W : Finset α) (p q : ℕ) :=
  {ab : OrderedLabelTuple W p × OrderedLabelTuple W q //
    Disjoint (tupleSubset ab.1).val (tupleSubset ab.2).val}

def tupleInitial {W : Finset α} {p q : ℕ} (t : OrderedLabelTuple W (p + q)) :
    OrderedLabelTuple W p :=
  ⟨fun i => t.val (Fin.castAdd q i),
    (fun _ _ h => Fin.ext (congrArg (fun k : Fin (p + q) => k.val) (t.property.1 h))),
    fun _ => t.property.2 _⟩

def tupleFinal {W : Finset α} {p q : ℕ} (t : OrderedLabelTuple W (p + q)) :
    OrderedLabelTuple W q :=
  ⟨fun i => t.val (Fin.natAdd p i),
    (fun _ _ h => Fin.ext (Nat.add_left_cancel
      (congrArg (fun k : Fin (p + q) => k.val) (t.property.1 h)))), fun _ => t.property.2 _⟩

omit [Fintype α] in
theorem tupleInitial_final_disjoint {W : Finset α} {p q : ℕ}
    (t : OrderedLabelTuple W (p + q)) :
    Disjoint (tupleSubset (tupleInitial t)).val (tupleSubset (tupleFinal t)).val := by
  apply disjoint_left.mpr
  intro a ha hb
  obtain ⟨i, hi⟩ := (mem_tupleSubset _ _).mp ha
  obtain ⟨j, hj⟩ := (mem_tupleSubset _ _).mp hb
  have h := t.property.1 (hi.trans hj.symm)
  have hv := congrArg Fin.val h
  simp only [Fin.val_castAdd, Fin.val_natAdd] at hv
  omega

def tupleSplit {W : Finset α} {p q : ℕ} (t : OrderedLabelTuple W (p + q)) :
    DisjointOrderedTuplePair W p q :=
  ⟨(tupleInitial t, tupleFinal t), tupleInitial_final_disjoint t⟩

def tupleJoin {W : Finset α} {p q : ℕ} (ab : DisjointOrderedTuplePair W p q) :
    OrderedLabelTuple W (p + q) :=
  ⟨Fin.append ab.val.1.val ab.val.2.val,
    Fin.append_injective_iff.mpr ⟨ab.val.1.property.1, ab.val.2.property.1, by
      intro i j hij
      exact disjoint_left.mp ab.property
        ((mem_tupleSubset _ _).mpr ⟨i, rfl⟩) ((mem_tupleSubset _ _).mpr ⟨j, hij.symm⟩)⟩,
    by
      intro k
      refine Fin.addCases (fun i => ?_) (fun j => ?_) k
      · simpa only [Fin.append_left] using ab.val.1.property.2 i
      · simpa only [Fin.append_right] using ab.val.2.property.2 j⟩

omit [Fintype α] in
@[simp]
theorem tupleInitial_join {W : Finset α} {p q : ℕ} (ab : DisjointOrderedTuplePair W p q) :
    tupleInitial (tupleJoin ab) = ab.val.1 := by
  apply Subtype.ext
  funext i
  exact Fin.append_left _ _ i

omit [Fintype α] in
@[simp]
theorem tupleFinal_join {W : Finset α} {p q : ℕ} (ab : DisjointOrderedTuplePair W p q) :
    tupleFinal (tupleJoin ab) = ab.val.2 := by
  apply Subtype.ext
  funext i
  exact Fin.append_right _ _ i

omit [Fintype α] in
@[simp]
theorem tupleJoin_split {W : Finset α} {p q : ℕ} (t : OrderedLabelTuple W (p + q)) :
    tupleJoin (tupleSplit t) = t := by
  apply Subtype.ext
  exact Fin.append_castAdd_natAdd

/-- The exact word-to-pair bijection at a cut without preservation. -/
def orderedTupleSplitEquiv (W : Finset α) (p q : ℕ) :
    OrderedLabelTuple W (p + q) ≃ DisjointOrderedTuplePair W p q where
  toFun := tupleSplit
  invFun := tupleJoin
  left_inv := tupleJoin_split
  right_inv ab := by
    apply Subtype.ext
    exact Prod.ext (tupleInitial_join ab) (tupleFinal_join ab)

omit [Fintype α] in
@[simp]
theorem orderedTupleList_join {W : Finset α} {p q : ℕ}
    (ab : DisjointOrderedTuplePair W p q) :
    orderedTupleList (tupleJoin ab) =
      orderedTupleList ab.val.1 ++ orderedTupleList ab.val.2 :=
  List.ofFn_fin_append _ _

omit [Fintype α] in
theorem tupleSubset_join {W : Finset α} {p q : ℕ}
    (ab : DisjointOrderedTuplePair W p q) :
    (tupleSubset (tupleJoin ab)).val =
      (tupleSubset ab.val.1).val ∪ (tupleSubset ab.val.2).val := by
  rw [← toFinset_orderedTupleList, orderedTupleList_join, List.toFinset_append,
    toFinset_orderedTupleList, toFinset_orderedTupleList]

omit [Fintype α] in
theorem tupleSubset_initial_subset {W : Finset α} {p q : ℕ}
    (t : OrderedLabelTuple W (p + q)) :
    (tupleSubset (tupleInitial t)).val ⊆ (tupleSubset t).val := by
  intro a ha
  have h := tupleSubset_join (tupleSplit t)
  rw [tupleJoin_split] at h
  rw [h]
  exact mem_union_left _ ha

omit [Fintype α] in
theorem tupleSubset_final_subset {W : Finset α} {p q : ℕ}
    (t : OrderedLabelTuple W (p + q)) :
    (tupleSubset (tupleFinal t)).val ⊆ (tupleSubset t).val := by
  intro a ha
  have h := tupleSubset_join (tupleSplit t)
  rw [tupleJoin_split] at h
  rw [h]
  exact mem_union_right _ ha

theorem sum_orderedTuple_split {B : Type*} [AddCommMonoid B]
    (W : Finset α) (p q : ℕ) (f : OrderedLabelTuple W (p + q) → B) :
    (∑ t, f t) = ∑ ab : DisjointOrderedTuplePair W p q, f (tupleJoin ab) :=
  ((orderedTupleSplitEquiv W p q).symm.sum_comp f).symm

theorem sum_disjointOrderedTuplePair {B : Type*} [AddCommMonoid B]
    (W : Finset α) (p q : ℕ) (f : OrderedLabelTuple W p → OrderedLabelTuple W q → B) :
    (∑ ab : DisjointOrderedTuplePair W p q, f ab.val.1 ab.val.2) =
      ∑ a, ∑ b, if Disjoint (tupleSubset a).val (tupleSubset b).val then f a b else 0 := by
  classical
  rw [← Finset.sum_subtype (univ.filter fun ab : OrderedLabelTuple W p ×
      OrderedLabelTuple W q => Disjoint (tupleSubset ab.1).val (tupleSubset ab.2).val)
    (by simp) (fun ab => f ab.1 ab.2), sum_filter, Fintype.sum_prod_type]

def tupleSingleton {W : Finset α} (a : α) (ha : a ∈ W) : OrderedLabelTuple W 1 :=
  ⟨fun _ => a, (fun _ _ _ => Subsingleton.elim _ _), fun _ => ha⟩

omit [Fintype α] in
@[simp]
theorem tupleSubset_singleton {W : Finset α} (a : α) (ha : a ∈ W) :
    (tupleSubset (tupleSingleton a ha)).val = {a} := by
  ext b
  simp [tupleSubset, tupleSingleton, eq_comm]

omit [Fintype α] [DecidableEq α] in
@[simp]
theorem orderedTupleList_singleton {W : Finset α} (a : α) (ha : a ∈ W) :
    orderedTupleList (tupleSingleton a ha) = [a] := by
  simp [orderedTupleList, tupleSingleton, List.ofFn_succ]

def tuplePairMissing {W : Finset α} {p q : ℕ} (hW : W.card = p + 1 + q)
    (ab : DisjointOrderedTuplePair W p q) : α :=
  missingWordLabel W (by omega) (tupleSubset ab.val.1) (tupleSubset ab.val.2) ab.property

omit [Fintype α] in
theorem tuplePairMissing_spec {W : Finset α} {p q : ℕ} (hW : W.card = p + 1 + q)
    (ab : DisjointOrderedTuplePair W p q) :
    W \ ((tupleSubset ab.val.1).val ∪ (tupleSubset ab.val.2).val) =
      {tuplePairMissing hW ab} :=
  missingWordLabel_spec W (by omega) (tupleSubset ab.val.1) (tupleSubset ab.val.2) ab.property

omit [Fintype α] in
omit [Fintype α] in
theorem tuplePairMissing_mem_sdiff {W : Finset α} {p q : ℕ} (hW : W.card = p + 1 + q)
    (ab : DisjointOrderedTuplePair W p q) :
    tuplePairMissing hW ab ∈ W \ ((tupleSubset ab.val.1).val ∪ (tupleSubset ab.val.2).val) := by
  rw [tuplePairMissing_spec]
  exact mem_singleton_self _

omit [Fintype α] in
theorem tuplePairMissing_mem {W : Finset α} {p q : ℕ} (hW : W.card = p + 1 + q)
    (ab : DisjointOrderedTuplePair W p q) : tuplePairMissing hW ab ∈ W :=
  (mem_sdiff.mp (tuplePairMissing_mem_sdiff hW ab)).1

omit [Fintype α] in
theorem tuplePairMissing_not_initial {W : Finset α} {p q : ℕ} (hW : W.card = p + 1 + q)
    (ab : DisjointOrderedTuplePair W p q) :
    tuplePairMissing hW ab ∉ (tupleSubset ab.val.1).val := by
  intro ha
  exact (mem_sdiff.mp (tuplePairMissing_mem_sdiff hW ab)).2 (mem_union_left _ ha)

omit [Fintype α] in
theorem tuplePairMissing_not_final {W : Finset α} {p q : ℕ} (hW : W.card = p + 1 + q)
    (ab : DisjointOrderedTuplePair W p q) :
    tuplePairMissing hW ab ∉ (tupleSubset ab.val.2).val := by
  intro hb
  exact (mem_sdiff.mp (tuplePairMissing_mem_sdiff hW ab)).2 (mem_union_right _ hb)

def tupleMissingPrefix {W : Finset α} {p q : ℕ} (hW : W.card = p + 1 + q)
    (ab : DisjointOrderedTuplePair W p q) : DisjointOrderedTuplePair W p 1 :=
  ⟨(ab.val.1, tupleSingleton (tuplePairMissing hW ab) (tuplePairMissing_mem hW ab)), by
    rw [tupleSubset_singleton, disjoint_singleton_right]
    exact tuplePairMissing_not_initial hW ab⟩

def tupleMissingJoinPair {W : Finset α} {p q : ℕ} (hW : W.card = p + 1 + q)
    (ab : DisjointOrderedTuplePair W p q) : DisjointOrderedTuplePair W (p + 1) q :=
  ⟨(tupleJoin (tupleMissingPrefix hW ab), ab.val.2), by
    rw [tupleSubset_join, disjoint_union_left]
    constructor
    · exact ab.property
    · simpa only [tupleMissingPrefix, tupleSubset_singleton, disjoint_singleton_left] using
        tuplePairMissing_not_final hW ab⟩

/-- Insert the missing label between the two subwords. -/
def tupleInsertMiddle {W : Finset α} {p q : ℕ} (hW : W.card = p + 1 + q)
    (ab : DisjointOrderedTuplePair W p q) : OrderedLabelTuple W (p + 1 + q) :=
  tupleJoin (tupleMissingJoinPair hW ab)

/-- Drop the distinguished middle position of a word. -/
def tupleDropMiddle {W : Finset α} {p q : ℕ}
    (t : OrderedLabelTuple W (p + 1 + q)) : DisjointOrderedTuplePair W p q :=
  ⟨(tupleInitial (tupleInitial t), tupleFinal t),
    (tupleInitial_final_disjoint t).mono_left (tupleSubset_initial_subset (tupleInitial t))⟩

def tupleMiddle {W : Finset α} {p q : ℕ} (t : OrderedLabelTuple W (p + 1 + q)) : α :=
  (tupleFinal (tupleInitial t)).val 0

omit [Fintype α] in
theorem tupleMiddle_mem_sdiff {W : Finset α} {p q : ℕ}
    (t : OrderedLabelTuple W (p + 1 + q)) :
    tupleMiddle t ∈ W \ ((tupleSubset (tupleDropMiddle t).val.1).val ∪
      (tupleSubset (tupleDropMiddle t).val.2).val) := by
  let a := tupleFinal (tupleInitial t)
  have ha : tupleMiddle t ∈ (tupleSubset a).val := (mem_tupleSubset _ _).mpr ⟨0, rfl⟩
  have hw : tupleMiddle t ∈ W := a.property.2 0
  refine mem_sdiff.mpr ⟨hw, ?_⟩
  intro hmem
  rcases mem_union.mp hmem with hi | hf
  · exact disjoint_left.mp (tupleInitial_final_disjoint (tupleInitial t)) hi ha
  · exact disjoint_left.mp (tupleInitial_final_disjoint t)
      (tupleSubset_final_subset (tupleInitial t) ha) hf

omit [Fintype α] in
theorem tuplePairMissing_dropMiddle {W : Finset α} {p q : ℕ} (hW : W.card = p + 1 + q)
    (t : OrderedLabelTuple W (p + 1 + q)) :
    tuplePairMissing hW (tupleDropMiddle t) = tupleMiddle t := by
  have h := tupleMiddle_mem_sdiff t
  rw [tuplePairMissing_spec hW (tupleDropMiddle t), mem_singleton] at h
  exact h.symm

omit [Fintype α] in
@[simp]
theorem tupleDropMiddle_insertMiddle {W : Finset α} {p q : ℕ} (hW : W.card = p + 1 + q)
    (ab : DisjointOrderedTuplePair W p q) :
    tupleDropMiddle (tupleInsertMiddle hW ab) = ab := by
  apply Subtype.ext
  apply Prod.ext
  · change tupleInitial (tupleInitial (tupleJoin (tupleMissingJoinPair hW ab))) = ab.val.1
    rw [tupleInitial_join]
    change tupleInitial (tupleJoin (tupleMissingPrefix hW ab)) = ab.val.1
    exact tupleInitial_join _
  · change tupleFinal (tupleJoin (tupleMissingJoinPair hW ab)) = ab.val.2
    exact tupleFinal_join _

omit [Fintype α] in
theorem tupleInsertMiddle_dropMiddle {W : Finset α} {p q : ℕ} (hW : W.card = p + 1 + q)
    (t : OrderedLabelTuple W (p + 1 + q)) :
    tupleInsertMiddle hW (tupleDropMiddle t) = t := by
  have hm : tupleSingleton (tuplePairMissing hW (tupleDropMiddle t))
      (tuplePairMissing_mem hW (tupleDropMiddle t)) = tupleFinal (tupleInitial t) := by
    apply Subtype.ext
    funext i
    rw [Subsingleton.elim i 0]
    exact tuplePairMissing_dropMiddle hW t
  have hp : tupleJoin (tupleMissingPrefix hW (tupleDropMiddle t)) = tupleInitial t := by
    have hpair : tupleMissingPrefix hW (tupleDropMiddle t) = tupleSplit (tupleInitial t) := by
      apply Subtype.ext
      exact Prod.ext rfl hm
    rw [hpair, tupleJoin_split]
  have hpair : tupleMissingJoinPair hW (tupleDropMiddle t) = tupleSplit t := by
    apply Subtype.ext
    exact Prod.ext hp rfl
  unfold tupleInsertMiddle
  rw [hpair, tupleJoin_split]

/-- The preservation-cut bijection recovers the omitted middle letter
from the complementary singleton of the two retained subwords. -/
def orderedTupleMiddleEquiv (W : Finset α) (p q : ℕ) (hW : W.card = p + 1 + q) :
    OrderedLabelTuple W (p + 1 + q) ≃ DisjointOrderedTuplePair W p q where
  toFun := tupleDropMiddle
  invFun := tupleInsertMiddle hW
  left_inv := tupleInsertMiddle_dropMiddle hW
  right_inv := tupleDropMiddle_insertMiddle hW

omit [Fintype α] in
@[simp]
theorem tupleMiddle_insertMiddle {W : Finset α} {p q : ℕ}
    (hW : W.card = p + 1 + q) (ab : DisjointOrderedTuplePair W p q) :
    tupleMiddle (tupleInsertMiddle hW ab) = tuplePairMissing hW ab := by
  have h := tuplePairMissing_dropMiddle hW (tupleInsertMiddle hW ab)
  rw [tupleDropMiddle_insertMiddle] at h
  exact h.symm

omit [Fintype α] in
theorem orderedTupleList_insertMiddle {W : Finset α} {p q : ℕ}
    (hW : W.card = p + 1 + q) (ab : DisjointOrderedTuplePair W p q) :
    orderedTupleList (tupleInsertMiddle hW ab) =
      orderedTupleList ab.val.1 ++ tuplePairMissing hW ab :: orderedTupleList ab.val.2 := by
  unfold tupleInsertMiddle
  rw [orderedTupleList_join]
  change orderedTupleList (tupleJoin (tupleMissingPrefix hW ab)) ++ orderedTupleList ab.val.2 = _
  rw [orderedTupleList_join]
  simp only [tupleMissingPrefix, orderedTupleList_singleton, List.append_assoc,
    List.singleton_append]

theorem sum_orderedTuple_middle {B : Type*} [AddCommMonoid B]
    (W : Finset α) (p q : ℕ) (hW : W.card = p + 1 + q)
    (f : OrderedLabelTuple W (p + 1 + q) → B) :
    (∑ t, f t) = ∑ ab : DisjointOrderedTuplePair W p q, f (tupleInsertMiddle hW ab) :=
  ((orderedTupleMiddleEquiv W p q hW).symm.sum_comp f).symm

end

end KadisonKastler

end OAI
