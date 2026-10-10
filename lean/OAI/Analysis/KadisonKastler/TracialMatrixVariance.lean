import OAI.Analysis.KadisonKastler.TracialFiniteAveraging
import OAI.Analysis.KadisonKastler.MatrixAveraging
import OAI.Analysis.KadisonKastler.FiniteMatrixPolar
import Mathlib.Data.Matrix.Composition

namespace OAI

/-! # Uniform variance control for the finite matrix coordinates -/

namespace KadisonKastler

open scoped BigOperators

noncomputable section

local instance : PartialOrder ℂ := CStarAlgebra.spectralOrder _
local instance : StarOrderedRing ℂ := CStarAlgebra.spectralOrderedRing _

variable {ι A : Type*} [Fintype ι] [DecidableEq ι] [CStarAlgebra A]

def standardAlgebraicMatrixUnits : Generator.MatrixUnitSystem ι (Matrix ι ι ℂ) where
  entry i j := Matrix.single i j 1
  star_entry i j := by simp only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_single, star_one]
  mul_entry i j k l := by
    by_cases h : j = k
    · subst k; simp
    · simp [Matrix.single_mul_single_of_ne, h]
  total := Matrix.sum_single_one

@[simp] theorem standardAlgebraicMatrixUnits_hom (a : Matrix ι ι ℂ) :
    standardAlgebraicMatrixUnits.hom a = a := by
  ext i j
  simp [Generator.MatrixUnitSystem.hom_apply, standardAlgebraicMatrixUnits, Matrix.single,
    Matrix.sum_apply, ite_and]

def matrixUnitsOfEquiv (e : Matrix ι ι ℂ ≃⋆ₐ[ℂ] A) : Generator.MatrixUnitSystem ι A :=
  standardAlgebraicMatrixUnits.map e.toStarAlgHom

theorem matrixUnitsOfEquiv_hom (e : Matrix ι ι ℂ ≃⋆ₐ[ℂ] A) (a : Matrix ι ι ℂ) :
    (matrixUnitsOfEquiv e).hom a = e a := by
  change (∑ i, ∑ j, a i j • e (standardAlgebraicMatrixUnits.entry i j)) = e a
  calc
    _ = e (∑ i, ∑ j, a i j • standardAlgebraicMatrixUnits.entry i j) := by
      simp only [map_sum, map_smul]
    _ = e a := congrArg e (standardAlgebraicMatrixUnits_hom a)

theorem matrixUnitsOfEquiv_surjective (e : Matrix ι ι ℂ ≃⋆ₐ[ℂ] A) :
    Function.Surjective (matrixUnitsOfEquiv e).hom := by
  intro a
  exact ⟨e.symm a, by rw [matrixUnitsOfEquiv_hom, e.apply_symm_apply]⟩

def finiteMatrixFlatten (n j : ℕ) : FiniteMatrixModel n j ≃⋆ₐ[ℂ]
    Matrix (Fin n × Fin (j + 1)) (Fin n × Fin (j + 1)) ℂ where
  __ := Matrix.compAlgEquiv (Fin n) (Fin (j + 1)) ℂ ℂ
  map_star' _ := rfl
  map_smul' _ _ := rfl

local instance (n j : ℕ) [NeZero n] : PartialOrder (FiniteMatrixModel n j) := CStarAlgebra.spectralOrder _
local instance (n j : ℕ) [NeZero n] : StarOrderedRing (FiniteMatrixModel n j) := CStarAlgebra.spectralOrderedRing _

theorem finiteMatrixModel_variance_control (n j : ℕ) [NeZero n] (x : FiniteMatrixModel n j) :
    ∃ u : unitary (FiniteMatrixModel n j),
      traceTwoNorm (finiteMatrixModelTrace n j)
        (x - (finiteMatrixModelTrace n j).toLinearMap x • 1) ≤
      2 * traceTwoNorm (finiteMatrixModelTrace n j) ((u : FiniteMatrixModel n j) * x - x * u) := by
  let E := matrixUnitsOfEquiv (finiteMatrixFlatten n j).symm
  apply exists_unitary_trace_variance_of_finite_group (finiteMatrixModelTrace n j)
    (matrixUnitSignedRepresentation E) ?_ x
  intro a ha
  apply finiteMatrixModel_scalar_center n j a
  intro b
  obtain ⟨m, rfl⟩ := matrixUnitsOfEquiv_surjective (finiteMatrixFlatten n j).symm b
  exact ((E.commute_algebra_iff a).mpr (commute_matrixUnits_of_signed E a ha) _ ⟨m, rfl⟩).eq

end

end KadisonKastler

end OAI
