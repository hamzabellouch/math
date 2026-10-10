import OAI.GroupTheory.PolycyclicRecognition.Geometry.TupleBarBoundaryRecursion
import OAI.GroupTheory.PolycyclicRecognition.Geometry.ListBarBoundaryGrade

namespace OAI

/-! # The list differential agrees with the actual integral bar differential -/

noncomputable section
namespace PolycyclicRecognition
open CategoryTheory
attribute [local instance 2000] Rep.hV2 Rep.instLinear
variable {A : Type} [Group A]

omit [Group A] in
theorem listBarTail_tuple (n : ℕ) (v : Fin (n + 1) → A) :
    listBarTail (tupleBarToList (n + 1) (Finsupp.single v 1)) =
      tupleBarToList n (Finsupp.single (fun i => v i.succ) 1) := by
  simp only [tupleBarToList_single, List.ofFn_succ, listBarTail_single, listBarTailValue]

theorem listBarHeadMultiply_tuple (n : ℕ) (a : A) (v : Fin (n + 1) → A) :
    listBarHeadMultiply a (tupleBarToList (n + 1) (Finsupp.single v 1)) =
      tupleBarToList (n + 1) (Finsupp.single (Fin.cons (a * v 0) (fun i => v i.succ)) 1) := by
  simp only [tupleBarToList_single, List.ofFn_cons]
  rw [List.ofFn_succ, listBarHeadMultiply_single]

theorem tupleBarToList_d_single (n : ℕ) (v : Fin (n + 1) → A) :
    tupleBarToList n
      (groupHomology.inhomogeneousChains.d (integralTrivialCoefficient A) n
        (Finsupp.single v 1)) =
      listBarBoundary (tupleBarToList (n + 1) (Finsupp.single v 1)) := by
  induction n with
  | zero =>
    have hz : groupHomology.inhomogeneousChains.d (integralTrivialCoefficient A) 0
        (Finsupp.single v 1) = 0 := by
      rw [groupHomology.inhomogeneousChains.d_single]
      change (Finsupp.single (fun i : Fin 0 => v i.succ) (1 : ℤ) +
        ∑ j : Fin 1, (-1 : ℤ) ^ (j.val + 1) •
          Finsupp.single (Fin.contractNth j (· * ·) v) 1) = 0
      rw [Fin.sum_univ_one]
      have he : (fun i : Fin 0 => v i.succ) = Fin.contractNth 0 (· * ·) v := Subsingleton.elim _ _
      simp only [Fin.val_zero, zero_add, pow_one, neg_smul, one_smul, he, add_neg_cancel]
    rw [hz, map_zero]
    simp only [tupleBarToList_single, List.ofFn_succ, List.ofFn_zero,
      listBarBoundary_single, listBarBoundaryValue]
  | succ n ih =>
    obtain ⟨a, w, rfl⟩ := Fin.exists_cons v
    rw [tupleBarBoundary_cons, map_sub, map_add, map_sub,
      tupleBarToList_prepend, tupleBarToList_prepend, ih]
    conv_rhs => rw [← tupleBarPrepend_single (n + 1) a w (1 : ℤ),
      tupleBarToList_prepend, listBarBoundary_prepend]
    rw [listBarTail_tuple, listBarHeadMultiply_tuple]

theorem tupleBarToList_d (n : ℕ) (z : (Fin (n + 1) → A) →₀ ℤ) :
    tupleBarToList n
      (groupHomology.inhomogeneousChains.d (integralTrivialCoefficient A) n z) =
      listBarBoundary (tupleBarToList (n + 1) z) := by
  induction z using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | single v c =>
    rw [← Finsupp.smul_single_one v c]
    simpa only [map_smul] using congrArg (c • ·) (tupleBarToList_d_single n v)

end PolycyclicRecognition

end

end OAI
