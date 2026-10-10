import OAI.GroupTheory.PolycyclicRecognition.Algebra.ListBarInsertionHomotopy

namespace OAI

/-! # The integral shuffle prism proving additivity of a bar insertion -/

noncomputable section
namespace PolycyclicRecognition
variable {A : Type}

theorem listBarTail_pair (a b : A) (z : ListBarChain A) :
    listBarTail (listBarPair a b z) = listBarInsert b z + listBarPair a b (listBarTail z) := by
  induction z using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]; abel
  | single v n =>
    rw [← Finsupp.smul_single_one v n]
    simp only [map_smul, listBarPair_single, listBarTail_single, listBarInsert_single,
      ← smul_add]
    congr 1
    cases v with
    | nil => simp [listBarPairValue, listBarInsertValue, listBarTailValue]
    | cons c v =>
      rw [listBarPairValue, map_add, listBarTail_prepend, listBarTail_prepend,
        listBarTailValue, listBarPair_single]

theorem listBarHeadMultiply_pair [Mul A] (a b c : A) (z : ListBarChain A) :
    listBarHeadMultiply c (listBarPair a b z) =
      listBarPrepend (c * a) (listBarInsert b z) +
        listBarPair a b (listBarHeadMultiply c z) -
          listBarPrepend a (listBarInsert b (listBarHeadMultiply c z)) := by
  induction z using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]; abel
  | single v n =>
    rw [← Finsupp.smul_single_one v n]
    simp only [map_smul, listBarPair_single, listBarHeadMultiply_single,
      listBarInsert_single, ← smul_add, ← smul_sub]
    congr 1
    cases v with
    | nil => simp [listBarPairValue, listBarInsertValue]
    | cons d v =>
      simp only [listBarPairValue, map_add, listBarHeadMultiply_prepend]
      abel

theorem listBarBoundary_pair_step [CommSemigroup A] (a b c : A) (z : ListBarChain A)
    (ih : listBarBoundary (listBarPair a b z) = listBarInsert b z -
      listBarInsert (a * b) z + listBarInsert a z + listBarPair a b (listBarBoundary z)) :
    listBarBoundary (listBarPair a b (listBarPrepend c z)) =
      listBarInsert b (listBarPrepend c z) - listBarInsert (a * b) (listBarPrepend c z) +
        listBarInsert a (listBarPrepend c z) +
          listBarPair a b (listBarBoundary (listBarPrepend c z)) := by
  rw [listBarPair_prepend, map_add, listBarBoundary_prepend, listBarBoundary_prepend,
    listBarBoundary_insert, ih, listBarTail_pair, listBarHeadMultiply_pair]
  simp only [listBarBoundary_prepend]
  simp only [listBarTail_insert, listBarHeadMultiply_insert, listBarTail_prepend,
    listBarHeadMultiply_prepend, map_add, map_sub, map_neg]
  simp only [listBarPair_prepend, listBarInsert_prepend, map_sub]
  rw [mul_comm b a, mul_comm c a]
  abel

theorem listBarBoundary_pair [CommSemigroup A] (a b : A) (z : ListBarChain A) :
    listBarBoundary (listBarPair a b z) = listBarInsert b z - listBarInsert (a * b) z +
      listBarInsert a z + listBarPair a b (listBarBoundary z) := by
  have hs (v : List A) :
      listBarBoundary (listBarPair a b (Finsupp.single v 1)) =
        listBarInsert b (Finsupp.single v 1) - listBarInsert (a * b) (Finsupp.single v 1) +
          listBarInsert a (Finsupp.single v 1) +
            listBarPair a b (listBarBoundary (Finsupp.single v 1)) := by
    induction v with
    | nil => simp [listBarPairValue, listBarInsertValue, listBarBoundaryValue]
    | cons c v ih =>
      rw [← listBarPrepend_single c v (1 : ℤ)]
      exact listBarBoundary_pair_step a b c _ ih
  induction z using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]; abel
  | single v n =>
    rw [← Finsupp.smul_single_one v n]
    simpa only [map_smul, ← smul_add, ← smul_sub] using congrArg (n • ·) (hs v)

end PolycyclicRecognition

end

end OAI
