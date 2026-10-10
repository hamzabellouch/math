import OAI.GroupTheory.PolycyclicRecognition.Algebra.TupleBarInsertion
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

namespace OAI

/-! # Product cochains evaluate the integral bar product to a determinant -/

noncomputable section
namespace PolycyclicRecognition
variable {A K : Type} [CommRing K]

def tupleBarEvaluation {n : ℕ} (f : Fin n → A → K) :
    ((Fin n → A) →₀ ℤ) →ₗ[ℤ] K :=
  Finsupp.linearCombination ℤ (fun v => ∏ i, f i (v i))

@[simp] theorem tupleBarEvaluation_single {n : ℕ} (f : Fin n → A → K)
    (v : Fin n → A) (c : ℤ) :
    tupleBarEvaluation f (Finsupp.single v c) = c • ∏ i, f i (v i) := by
  simp [tupleBarEvaluation]

theorem tupleBarEvaluation_insert {n : ℕ} (f : Fin (n + 1) → A → K) (a : A)
    (z : (Fin n → A) →₀ ℤ) :
    tupleBarEvaluation f (tupleBarInsert n a z) =
      ∑ i : Fin (n + 1), (-1 : ℤ) ^ i.val •
        (f i a * tupleBarEvaluation (fun j => f (i.succAbove j)) z) := by
  have hs (v : Fin n → A) : tupleBarEvaluation f (tupleBarInsert n a (Finsupp.single v 1)) =
      ∑ i : Fin (n + 1), (-1 : ℤ) ^ i.val •
        (f i a * tupleBarEvaluation (fun j => f (i.succAbove j)) (Finsupp.single v 1)) := by
    simp only [tupleBarInsert, LinearMap.sum_apply, LinearMap.smul_apply,
      Finsupp.lmapDomain_apply, Finsupp.mapDomain_single, map_sum, map_smul,
      tupleBarEvaluation_single, one_smul]
    apply Finset.sum_congr rfl
    intro i _
    congr 1
    let w : Fin (n + 1) → A := i.insertNth a v
    change (∏ j : Fin (n + 1), f j (w j)) = _
    rw [Fin.prod_univ_succAbove (fun j => f j (w j)) i]
    dsimp only [w]
    simp only [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove]
  induction z using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy =>
    simp only [map_add, hx, hy, mul_add, smul_add, Finset.sum_add_distrib]
  | single v c =>
    rw [← Finsupp.smul_single_one v c, map_smul, map_smul, hs, Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [map_smul, mul_smul_comm, smul_comm]

theorem tupleBarEvaluation_product {n : ℕ} (f : Fin n → A → K) (v : Fin n → A) :
    tupleBarEvaluation f (tupleBarProduct v) = Matrix.det (fun i j => f i (v j)) := by
  induction n with
  | zero =>
    have he : tupleBarProduct v = Finsupp.single v 1 := by
      apply tupleBarToList_injective 0
      simp only [tupleBarProduct_toList, tupleBarToList_single, List.ofFn_zero, listBarProduct]
    rw [he, tupleBarEvaluation_single]
    simp only [Finset.univ_eq_empty, Finset.prod_empty, one_smul]
    exact Matrix.det_isEmpty.symm
  | succ n ih =>
    obtain ⟨a, w, rfl⟩ := Fin.exists_cons v
    rw [tupleBarProduct_cons, tupleBarEvaluation_insert]
    erw [Matrix.det_succ_column_zero]
    apply Finset.sum_congr rfl
    intro i _
    rw [ih]
    have hm : Matrix.submatrix (fun k l => f k ((Fin.cons a w : Fin (n + 1) → A) l))
        i.succAbove Fin.succ =
        (fun k l => f (i.succAbove k) (w l)) := by
      ext k l
      rfl
    rw [hm]
    simp only [Fin.cons_zero, zsmul_eq_mul, Int.cast_pow, Int.cast_neg, Int.cast_one]
    rw [mul_assoc]

end PolycyclicRecognition

end

end OAI
