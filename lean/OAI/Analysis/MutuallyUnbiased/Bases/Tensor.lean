import OAI.Analysis.MutuallyUnbiased.Bases.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Data.Fintype.BigOperators

namespace OAI

/-! Explicit mutually unbiased bases from two- and three-dimensional unitary matrices. -/

noncomputable section
open scoped BigOperators ComplexConjugate
namespace MUB6.ThreeTensor

abbrev MatrixTwo := Matrix (Fin 2) (Fin 2) ℂ
abbrev MatrixThree := Matrix (Fin 3) (Fin 3) ℂ

def coordEquiv : Fin 2 × Fin 3 ≃ Coord := finProdFinEquiv

def tensorMatrix (A : MatrixTwo) (B : MatrixThree) : CMatrix :=
  fun i j => A (coordEquiv.symm i).1 (coordEquiv.symm j).1 *
    B (coordEquiv.symm i).2 (coordEquiv.symm j).2

lemma tensor_cross (A C : MatrixTwo) (B D : MatrixThree) (i j : Coord) :
    ((tensorMatrix A B).conjTranspose * tensorMatrix C D) i j =
      (A.conjTranspose * C) (coordEquiv.symm i).1 (coordEquiv.symm j).1 *
      (B.conjTranspose * D) (coordEquiv.symm i).2 (coordEquiv.symm j).2 := by
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply]
  rw [← coordEquiv.sum_comp]
  simp only [tensorMatrix, Equiv.symm_apply_apply]
  rw [Fintype.sum_prod_type]
  conv_rhs => rw [Finset.sum_mul]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  rw [star_mul]
  ring

lemma tensor_gram (A : MatrixTwo) (B : MatrixThree)
    (hA : A.conjTranspose * A = 1) (hB : B.conjTranspose * B = 1) :
    (tensorMatrix A B).conjTranspose * tensorMatrix A B = 1 := by
  ext i j
  rw [tensor_cross, hA, hB]
  by_cases hij : i = j
  · subst j
    simp
  · have hp : coordEquiv.symm i ≠ coordEquiv.symm j :=
      fun h => hij (coordEquiv.symm.injective h)
    by_cases h₁ : (coordEquiv.symm i).1 = (coordEquiv.symm j).1
    · have h₂ : (coordEquiv.symm i).2 ≠ (coordEquiv.symm j).2 :=
        fun h => hp (Prod.ext h₁ h)
      simp [Matrix.one_apply, hij, h₁, h₂]
    · simp [Matrix.one_apply, hij, h₁]

def columns (H : CMatrix) (j : Coord) : Space :=
  WithLp.toLp 2 (fun i => H i j)

lemma columns_inner (H K : CMatrix) (i j : Coord) :
    inner ℂ (columns H i) (columns K j) = (H.conjTranspose * K) i j := by
  simp only [columns, PiLp.inner_apply, RCLike.inner_apply',
    Matrix.mul_apply, Matrix.conjTranspose_apply, starRingEnd_apply]

lemma columns_orthonormal (H : CMatrix) (hH : H.conjTranspose * H = 1) :
    Orthonormal ℂ (columns H) := by
  rw [orthonormal_iff_ite]
  intro i j
  rw [columns_inner, hH]
  exact Matrix.one_apply

def matrixBasis (H : CMatrix) (hH : H.conjTranspose * H = 1) : Basis :=
  OrthonormalBasis.mk (columns_orthonormal H hH)
    (((columns_orthonormal H hH).linearIndependent.span_eq_top_of_card_eq_finrank'
      (by simp [Space, Coord])).ge)

@[simp] lemma matrixBasis_apply (H : CMatrix) (hH : H.conjTranspose * H = 1)
    (j : Coord) : matrixBasis H hH j = columns H j := by
  simp [matrixBasis]

theorem attainable_three_of_small_matrices
    (A : Fin 3 → MatrixTwo) (B : Fin 3 → MatrixThree)
    (hA : ∀ r, (A r).conjTranspose * A r = 1)
    (hB : ∀ r, (B r).conjTranspose * B r = 1)
    (hAcross : ∀ r s, r ≠ s → ∀ i j,
      Complex.normSq (((A r).conjTranspose * A s) i j) = (1 : ℝ) / 2)
    (hBcross : ∀ r s, r ≠ s → ∀ i j,
      Complex.normSq (((B r).conjTranspose * B s) i j) = (1 : ℝ) / 3) :
    Attainable 3 := by
  refine ⟨fun r => matrixBasis (tensorMatrix (A r) (B r))
    (tensor_gram (A r) (B r) (hA r) (hB r)), ?_⟩
  intro r s hrs i j
  simp only [matrixBasis_apply, columns_inner, tensor_cross, Complex.normSq_mul]
  rw [hAcross r s hrs, hBcross r s hrs]
  norm_num

end MUB6.ThreeTensor

end

end OAI
