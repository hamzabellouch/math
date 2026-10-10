import Mathlib
import OAI.Analysis.MatrixSigning.Machines.ComplexBridge

namespace OAI

section

namespace KS.W08

open Matrix
open scoped BigOperators

def embedComplexMatrix {m n : Type*} (A : Matrix m n KS.W01.RationalComplex) : Matrix m n ℂ :=
  Matrix.of (fun i j => KS.W01.toComplex (A i j))

@[simp] theorem embedComplexMatrix_apply {m n : Type*}
    (A : Matrix m n KS.W01.RationalComplex) (i : m) (j : n) :
    embedComplexMatrix A i j = KS.W01.toComplex (A i j) := rfl

theorem embedComplexMatrix_eq {m n : Type*} (A : Matrix m n KS.W01.RationalComplex) :
    embedComplexMatrix A = (fun i j => KS.W01.toComplex (A i j)) := rfl

theorem embedded_inverse_is_matrix_inverse {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n KS.W01.RationalComplex) :
    (embedComplexMatrix A)⁻¹ =
      @Inv.inv (Matrix n n ℂ) Matrix.inv (embedComplexMatrix A) := rfl

def realify {m n : Type*} (A : Matrix m n ℂ) : Matrix (m ⊕ m) (n ⊕ n) ℝ :=
  Matrix.fromBlocks (fun i j => (A i j).re) (fun i j => -(A i j).im)
    (fun i j => (A i j).im) (fun i j => (A i j).re)

def rationalRealify {m n : Type*} (A : Matrix m n KS.W01.RationalComplex) :
    Matrix (m ⊕ m) (n ⊕ n) ℚ :=
  Matrix.fromBlocks (fun i j => (A i j).1) (fun i j => -(A i j).2)
    (fun i j => (A i j).2) (fun i j => (A i j).1)

theorem rationalRealify_cast {m n : Type*} (A : Matrix m n KS.W01.RationalComplex) :
    (fun i j => (rationalRealify A i j : ℝ)) =
      realify (fun i j => KS.W01.toComplex (A i j)) := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [rationalRealify, realify, Matrix.fromBlocks, KS.W01.toComplex]

theorem realify_injective {m n : Type*} :
    Function.Injective (@realify m n) := by
  intro A B h
  apply Matrix.ext
  intro i j
  apply Complex.ext
  · exact congrFun (congrFun h (Sum.inl i)) (Sum.inl j)
  · exact congrFun (congrFun h (Sum.inr i)) (Sum.inl j)

theorem realify_mul {m n p : Type*} [Fintype n]
    (A : Matrix m n ℂ) (B : Matrix n p ℂ) :
    realify (A * B) = realify A * realify B := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [realify, Matrix.fromBlocks, Matrix.mul_apply, Fintype.sum_sum_type, Complex.mul_re,
      Complex.mul_im, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      Finset.sum_neg_distrib] <;> ring

@[simp] theorem realify_one {n : Type*} [DecidableEq n] :
    realify (1 : Matrix n n ℂ) = 1 := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [realify, Matrix.fromBlocks, Matrix.one_apply] <;> split_ifs <;> rfl

theorem realify_inverse_equation {n : Type*} [Fintype n] [DecidableEq n]
    (A B : Matrix n n ℂ) (h : A * B = 1) :
    realify A * realify B = 1 := by
  rw [← realify_mul, h, realify_one]

theorem realify_inv {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) (hA : IsUnit A.det) :
    realify (A⁻¹) = (realify A)⁻¹ := by
  symm
  apply Matrix.inv_eq_right_inv
  exact realify_inverse_equation A A⁻¹ (Matrix.mul_nonsing_inv A hA)

theorem rationalRealify_det_ne_zero {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n KS.W01.RationalComplex)
    (hA : IsUnit (Matrix.det (fun i j => KS.W01.toComplex (A i j)))) :
    (rationalRealify A).det ≠ 0 := by
  let C := embedComplexMatrix A
  have hr : (realify C).det ≠ 0 :=
    Matrix.det_ne_zero_of_right_inverse
      (realify_inverse_equation C C⁻¹ (Matrix.mul_nonsing_inv C hA))
  intro hz
  have hm : Matrix.det (fun i j => (rationalRealify A i j : ℝ)) = 0 := by
    change ((Rat.castHom ℝ).mapMatrix (rationalRealify A)).det = 0
    rw [← (Rat.castHom ℝ).map_det (rationalRealify A), hz, map_zero]
  rw [rationalRealify_cast] at hm
  exact hr hm

theorem rationalRealify_inverse_cast {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n KS.W01.RationalComplex)
    (hA : IsUnit (Matrix.det (fun i j => KS.W01.toComplex (A i j)))) :
    ((rationalRealify A)⁻¹).map (Rat.castHom ℝ) =
      realify ((embedComplexMatrix A)⁻¹) := by
  let Q := rationalRealify A
  let C := embedComplexMatrix A
  have hQ : IsUnit Q.det := isUnit_iff_ne_zero.mpr (rationalRealify_det_ne_zero A hA)
  have he : Q.map (Rat.castHom ℝ) * (Q⁻¹).map (Rat.castHom ℝ) = 1 := by
    have he := congrArg (fun M : Matrix (n ⊕ n) (n ⊕ n) ℚ =>
      M.map (Rat.castHom ℝ)) (Matrix.mul_nonsing_inv Q hQ)
    rw [Matrix.map_mul (f := Rat.castHom ℝ)] at he
    simpa using he
  have hc : Q.map (Rat.castHom ℝ) = realify C := rationalRealify_cast A
  calc
    (Q⁻¹).map (Rat.castHom ℝ) = (Q.map (Rat.castHom ℝ))⁻¹ :=
      (Matrix.inv_eq_right_inv he).symm
    _ = realify (C⁻¹) := by rw [hc, ← realify_inv C hA]

theorem complex_inverse_entry_from_rational {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n KS.W01.RationalComplex)
    (hA : IsUnit (Matrix.det (fun i j => KS.W01.toComplex (A i j)))) (i j : n) :
    KS.W01.toComplex (((rationalRealify A)⁻¹ (Sum.inl i) (Sum.inl j)),
      ((rationalRealify A)⁻¹ (Sum.inr i) (Sum.inl j))) =
      ((embedComplexMatrix A)⁻¹) i j := by
  have h := rationalRealify_inverse_cast A hA
  apply Complex.ext
  · simpa [KS.W01.toComplex, realify, Matrix.fromBlocks, Matrix.map_apply] using
      congrFun (congrFun h (Sum.inl i)) (Sum.inl j)
  · simpa [KS.W01.toComplex, realify, Matrix.fromBlocks, Matrix.map_apply] using
      congrFun (congrFun h (Sum.inr i)) (Sum.inl j)

def realifyVector {n : Type*} (v : n → ℂ) : n ⊕ n → ℝ :=
  Sum.elim (fun i => (v i).re) (fun i => (v i).im)

theorem realify_mulVec {m n : Type*} [Fintype n]
    (A : Matrix m n ℂ) (v : n → ℂ) :
    realifyVector (A *ᵥ v) = realify A *ᵥ realifyVector v := by
  funext i
  rcases i with i | i <;>
    simp [realifyVector, realify, Matrix.fromBlocks, Matrix.mulVec, dotProduct, Fintype.sum_sum_type,
      Complex.mul_re, Complex.mul_im, Finset.sum_add_distrib,
      Finset.sum_sub_distrib] <;> ring

end KS.W08

end

end OAI
