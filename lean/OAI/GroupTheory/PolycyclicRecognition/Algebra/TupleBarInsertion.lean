import OAI.GroupTheory.PolycyclicRecognition.Algebra.TupleBarProduct
import Mathlib.Algebra.BigOperators.Fin

namespace OAI

/-! # The signed insertion formula in finite tuple coordinates -/

noncomputable section
namespace PolycyclicRecognition
variable {A : Type}

theorem listBarInsertValue_ofFn (a : A) {n : ℕ} (v : Fin n → A) :
    listBarInsertValue a (List.ofFn v) =
      ∑ i : Fin (n + 1), (-1 : ℤ) ^ i.val •
        Finsupp.single (List.ofFn (i.insertNth a v)) 1 := by
  induction n with
  | zero => simp [listBarInsertValue]
  | succ n ih =>
    obtain ⟨b, w, rfl⟩ := Fin.exists_cons v
    rw [List.ofFn_cons, listBarInsertValue, Fin.sum_univ_succ, ih]
    simp only [Fin.val_zero, pow_zero, one_smul, Fin.insertNth_zero', List.ofFn_cons,
      Fin.insertNth_succ_cons, Fin.val_succ, map_sum, map_smul, listBarPrepend_single]
    rw [sub_eq_add_neg, ← Finset.sum_neg_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    rw [pow_succ, mul_neg_one, neg_smul]

def tupleBarInsert (n : ℕ) (a : A) :
    ((Fin n → A) →₀ ℤ) →ₗ[ℤ] ((Fin (n + 1) → A) →₀ ℤ) :=
  ∑ i : Fin (n + 1), (-1 : ℤ) ^ i.val •
    Finsupp.lmapDomain ℤ ℤ (fun v : Fin n → A => i.insertNth a v)

theorem tupleBarToList_insert (n : ℕ) (a : A) (z : (Fin n → A) →₀ ℤ) :
    tupleBarToList (n + 1) (tupleBarInsert n a z) =
      listBarInsert a (tupleBarToList n z) := by
  have hs (v : Fin n → A) : tupleBarToList (n + 1)
      (tupleBarInsert n a (Finsupp.single v 1)) =
      listBarInsert a (tupleBarToList n (Finsupp.single v 1)) := by
    simp only [tupleBarInsert, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul,
      Finsupp.lmapDomain_apply, Finsupp.mapDomain_single, tupleBarToList_single,
      listBarInsert_single, listBarInsertValue_ofFn]
  induction z using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | single v c =>
    rw [← Finsupp.smul_single_one v c]
    simpa only [map_smul] using congrArg (c • ·) (hs v)

theorem tupleBarProduct_cons {n : ℕ} (a : A) (v : Fin n → A) :
    tupleBarProduct (Fin.cons a v) = tupleBarInsert n a (tupleBarProduct v) := by
  apply tupleBarToList_injective (n + 1)
  rw [tupleBarToList_insert, tupleBarProduct_toList, tupleBarProduct_toList, List.ofFn_cons]
  rfl

end PolycyclicRecognition

end

end OAI
