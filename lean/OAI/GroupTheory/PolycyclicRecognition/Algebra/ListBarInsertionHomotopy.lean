import OAI.GroupTheory.PolycyclicRecognition.Geometry.ListBarBoundaryOperators

namespace OAI

/-! # The integral one-letter bar insertion is a degree-one chain map -/

noncomputable section
namespace PolycyclicRecognition
variable {A : Type}

theorem listBarTail_insert (a : A) (z : ListBarChain A) :
    listBarTail (listBarInsert a z) = z - listBarInsert a (listBarTail z) := by
  induction z using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]; abel
  | single v n =>
    rw [← Finsupp.smul_single_one v n]
    simp only [map_smul, listBarInsert_single, listBarTail_single, ← smul_sub]
    congr 1
    cases v with
    | nil => simp [listBarInsertValue, listBarTailValue]
    | cons b v =>
      rw [listBarInsertValue, map_sub, listBarTail_single, listBarTail_prepend,
        listBarTailValue, listBarTailValue, listBarInsert_single]

theorem listBarHeadMultiply_insert [CommSemigroup A] (a b : A) (z : ListBarChain A) :
    listBarHeadMultiply b (listBarInsert a z) = listBarPrepend (a * b) z +
      listBarInsert a (listBarHeadMultiply b z) -
        listBarPrepend a (listBarHeadMultiply b z) := by
  induction z using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]; abel
  | single v n =>
    rw [← Finsupp.smul_single_one v n]
    simp only [map_smul, listBarInsert_single, listBarHeadMultiply_single,
      listBarPrepend_single, ← smul_add, ← smul_sub]
    congr 1
    cases v with
    | nil => simp [listBarInsertValue, mul_comm]
    | cons c v =>
      simp only [listBarInsertValue, map_sub, listBarHeadMultiply_single,
        listBarHeadMultiply_prepend, mul_comm b a]
      abel

theorem listBarBoundary_insert [CommSemigroup A] (a : A) (z : ListBarChain A) :
    listBarBoundary (listBarInsert a z) = -listBarInsert a (listBarBoundary z) := by
  have hs (v : List A) :
      listBarBoundary (listBarInsert a (Finsupp.single v 1)) =
        -listBarInsert a (listBarBoundary (Finsupp.single v 1)) := by
    induction v with
    | nil => simp [listBarInsertValue, listBarBoundaryValue]
    | cons b v ih =>
      rw [← listBarPrepend_single b v (1 : ℤ), listBarInsert_prepend, map_sub,
        listBarBoundary_prepend, listBarBoundary_prepend, listBarBoundary_prepend]
      simp only [listBarTail_prepend, listBarHeadMultiply_prepend,
        listBarHeadMultiply_insert, listBarTail_insert, ih, map_add, map_sub,
        map_neg, listBarInsert_prepend]
      abel
  induction z using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy, neg_add_rev]; abel
  | single v n =>
    rw [← Finsupp.smul_single_one v n]
    simpa only [map_smul, smul_neg] using congrArg (n • ·) (hs v)

end PolycyclicRecognition

end

end OAI
