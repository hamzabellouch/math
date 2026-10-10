import OAI.GroupTheory.PolycyclicRecognition.Algebra.ListBarPairHomotopy

namespace OAI

/-! # Integral alternating bar products and their additive prism -/

noncomputable section
namespace PolycyclicRecognition
variable {A : Type}

theorem listBarInsert_square_zero (a : A) (z : ListBarChain A) :
    listBarInsert a (listBarInsert a z) = 0 := by
  have hs (v : List A) : listBarInsert a (listBarInsert a (Finsupp.single v 1)) = 0 := by
    induction v with
    | nil => simp [listBarInsertValue]
    | cons b v ih =>
      rw [← listBarPrepend_single b v (1 : ℤ)]
      simp only [listBarInsert_prepend, map_sub, ih, map_zero]
      abel
  induction z using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy, add_zero]
  | single v n =>
    rw [← Finsupp.smul_single_one v n, map_smul, map_smul, hs, smul_zero]

theorem listBarInsert_anticommute (a b : A) (z : ListBarChain A) :
    listBarInsert a (listBarInsert b z) = -listBarInsert b (listBarInsert a z) := by
  have hs (v : List A) : listBarInsert a (listBarInsert b (Finsupp.single v 1)) =
      -listBarInsert b (listBarInsert a (Finsupp.single v 1)) := by
    induction v with
    | nil => simp [listBarInsertValue]
    | cons c v ih =>
      rw [← listBarPrepend_single c v (1 : ℤ)]
      simp only [listBarInsert_prepend, map_sub, map_neg, ih]
      abel
  induction z using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy, neg_add_rev]; abel
  | single v n =>
    rw [← Finsupp.smul_single_one v n]
    simpa only [map_smul, smul_neg] using congrArg (n • ·) (hs v)

def listBarProduct : List A → ListBarChain A
  | [] => Finsupp.single [] 1
  | a :: v => listBarInsert a (listBarProduct v)

theorem listBarProduct_cycle [CommSemigroup A] (v : List A) :
    listBarBoundary (listBarProduct v) = 0 := by
  induction v with
  | nil => simp [listBarProduct, listBarBoundaryValue]
  | cons a v ih => rw [listBarProduct, listBarBoundary_insert, ih, map_zero, neg_zero]

theorem listBarProduct_mul_prism [CommSemigroup A] (a b : A) (v : List A) :
    listBarProduct ((a * b) :: v) = listBarProduct (a :: v) + listBarProduct (b :: v) -
      listBarBoundary (listBarPair a b (listBarProduct v)) := by
  rw [listBarBoundary_pair, listBarProduct_cycle, map_zero]
  simp only [listBarProduct]
  abel

end PolycyclicRecognition

end

end OAI
