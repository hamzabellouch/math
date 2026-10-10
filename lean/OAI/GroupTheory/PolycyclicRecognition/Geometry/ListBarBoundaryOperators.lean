import OAI.GroupTheory.PolycyclicRecognition.Algebra.ListBarShuffle

namespace OAI

/-! # Boundary identities used in the bar shuffle homotopies -/

noncomputable section
namespace PolycyclicRecognition
variable {A : Type}

def listBarTailValue : List A → ListBarChain A
  | [] => 0
  | _ :: v => Finsupp.single v 1

def listBarTail : ListBarChain A →ₗ[ℤ] ListBarChain A :=
  Finsupp.linearCombination ℤ listBarTailValue

@[simp] theorem listBarTail_single (v : List A) :
    listBarTail (Finsupp.single v 1) = listBarTailValue v := by simp [listBarTail]

def listBarHeadMultiply [Mul A] (a : A) : ListBarChain A →ₗ[ℤ] ListBarChain A :=
  Finsupp.lmapDomain ℤ ℤ (fun v => match v with
    | [] => []
    | b :: v => (a * b) :: v)

@[simp] theorem listBarHeadMultiply_single [Mul A] (a : A) (v : List A) (z : ℤ) :
    listBarHeadMultiply a (Finsupp.single v z) =
      Finsupp.single (match v with | [] => [] | b :: v => (a * b) :: v) z := by
  simp [listBarHeadMultiply]

theorem listBarTail_prepend (a : A) (z : ListBarChain A) :
    listBarTail (listBarPrepend a z) = z := by
  induction z using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | single v n =>
    rw [← Finsupp.smul_single_one v n, map_smul, map_smul,
      listBarPrepend_single, listBarTail_single]
    simp [listBarTailValue]

theorem listBarHeadMultiply_prepend [Mul A] (a b : A) (z : ListBarChain A) :
    listBarHeadMultiply a (listBarPrepend b z) = listBarPrepend (a * b) z := by
  induction z using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | single v n => simp only [listBarPrepend_single, listBarHeadMultiply_single]

theorem listBarBoundary_prepend [Mul A] (a : A) (z : ListBarChain A) :
    listBarBoundary (listBarPrepend a z) = z - listBarHeadMultiply a z +
      listBarPrepend a (listBarTail z) - listBarPrepend a (listBarBoundary z) := by
  induction z using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]; abel
  | single v n =>
    rw [← Finsupp.smul_single_one v n]
    simp only [map_smul, listBarPrepend_single, listBarBoundary_single,
      listBarHeadMultiply_single, listBarTail_single, ← smul_add, ← smul_sub]
    congr 1
    cases v with
    | nil => simp [listBarBoundaryValue, listBarTailValue]
    | cons b v => rfl

end PolycyclicRecognition

end

end OAI
