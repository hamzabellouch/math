import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.Tactic.Abel

namespace OAI

/-! # The one- and two-letter shuffle operators on abelian bar chains

List coordinates make the insertion homotopies recursive. Degree restrictions
will identify these operators with the ordinary finite-tuple bar complex.
-/

noncomputable section
namespace PolycyclicRecognition
variable {A : Type}

abbrev ListBarChain (A : Type) := List A →₀ ℤ

def listBarPrepend (a : A) : ListBarChain A →ₗ[ℤ] ListBarChain A :=
  Finsupp.lmapDomain ℤ ℤ (List.cons a)

@[simp] theorem listBarPrepend_single (a : A) (v : List A) (z : ℤ) :
    listBarPrepend a (Finsupp.single v z) = Finsupp.single (a :: v) z := by
  simp only [listBarPrepend, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]

section Boundary
variable [Mul A]

def listBarBoundaryValue : List A → ListBarChain A
  | [] => 0
  | [_] => 0
  | a :: b :: v => Finsupp.single (b :: v) 1 - Finsupp.single ((a * b) :: v) 1 +
      listBarPrepend a (Finsupp.single v 1) - listBarPrepend a (listBarBoundaryValue (b :: v))

def listBarBoundary : ListBarChain A →ₗ[ℤ] ListBarChain A :=
  Finsupp.linearCombination ℤ listBarBoundaryValue

@[simp] theorem listBarBoundary_single (v : List A) :
    listBarBoundary (Finsupp.single v 1) = listBarBoundaryValue v := by
  simp [listBarBoundary]

end Boundary

def listBarInsertValue (a : A) : List A → ListBarChain A
  | [] => Finsupp.single [a] 1
  | b :: v => Finsupp.single (a :: b :: v) 1 - listBarPrepend b (listBarInsertValue a v)

def listBarInsert (a : A) : ListBarChain A →ₗ[ℤ] ListBarChain A :=
  Finsupp.linearCombination ℤ (listBarInsertValue a)

@[simp] theorem listBarInsert_single (a : A) (v : List A) :
    listBarInsert a (Finsupp.single v 1) = listBarInsertValue a v := by
  simp [listBarInsert]

def listBarPairValue (a b : A) : List A → ListBarChain A
  | [] => Finsupp.single [a, b] 1
  | c :: v => listBarPrepend a (listBarInsertValue b (c :: v)) +
      listBarPrepend c (listBarPairValue a b v)

def listBarPair (a b : A) : ListBarChain A →ₗ[ℤ] ListBarChain A :=
  Finsupp.linearCombination ℤ (listBarPairValue a b)

@[simp] theorem listBarPair_single (a b : A) (v : List A) :
    listBarPair a b (Finsupp.single v 1) = listBarPairValue a b v := by
  simp [listBarPair]

theorem listBarInsert_prepend (a b : A) (z : ListBarChain A) :
    listBarInsert a (listBarPrepend b z) =
      listBarPrepend a (listBarPrepend b z) - listBarPrepend b (listBarInsert a z) := by
  induction z using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]; abel
  | single v n =>
    simp only [← Finsupp.smul_single_one v n, map_smul, listBarPrepend_single,
      listBarInsert_single, listBarInsertValue, smul_sub]

theorem listBarPair_prepend (a b c : A) (z : ListBarChain A) :
    listBarPair a b (listBarPrepend c z) =
      listBarPrepend a (listBarInsert b (listBarPrepend c z)) +
        listBarPrepend c (listBarPair a b z) := by
  induction z using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]; abel
  | single v n =>
    have he := listBarPairValue.eq_2 a b c v
    simpa only [← Finsupp.smul_single_one v n, map_smul, listBarPrepend_single,
      listBarPair_single, listBarInsert_single, smul_add] using congrArg (n • ·) he

end PolycyclicRecognition

end

end OAI
