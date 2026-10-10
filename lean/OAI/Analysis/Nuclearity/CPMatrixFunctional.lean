import OAI.Analysis.Nuclearity.CommutingMatrixPositive
import OAI.Analysis.Nuclearity.MatrixCPAmplification

namespace OAI

/-! A completely positive map to a finite matrix algebra defines a positive
functional on the matrix amplification. This is the scalar step in finite
matrix extension; the positivity calculation is an explicit matrix corner. -/

noncomputable section
open scoped ComplexOrder CStarAlgebra

namespace WeakPureInfiniteness

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  {n : ℕ}

def cpMatrixFunctionalLinear (φ : A →L[ℂ] CStarMatrix (Fin n) (Fin n) ℂ) :
    CStarMatrix (Fin n) (Fin n) A →ₗ[ℂ] ℂ where
  toFun M := ∑ i, ∑ j, φ (M i j) i j
  map_add' M N := by simp [Finset.sum_add_distrib]
  map_smul' c M := by simp [Finset.mul_sum]

omit [PartialOrder A] [StarOrderedRing A] in
@[simp] lemma cpMatrixFunctionalLinear_apply
    (φ : A →L[ℂ] CStarMatrix (Fin n) (Fin n) ℂ)
    (M : CStarMatrix (Fin n) (Fin n) A) :
    cpMatrixFunctionalLinear φ M = ∑ i, ∑ j, φ (M i j) i j := rfl

private lemma matrixUnit_corner_product (p i j : Fin n)
    (Y : CStarMatrix (Fin n) (Fin n) ℂ) :
    (star (matrixUnit i p) * Y * matrixUnit j p) p p = Y i j := by
  change (∑ k, (∑ l, star (if l = i ∧ p = p then (1 : ℂ) else 0) * Y l k) *
    (if k = j ∧ p = p then (1 : ℂ) else 0)) = Y i j
  simp


lemma cpMatrixFunctionalLinear_nonneg (p : Fin n)
    (φ : A →L[ℂ] CStarMatrix (Fin n) (Fin n) ℂ) (hφ : CompletelyPositive φ)
    (M : CStarMatrix (Fin n) (Fin n) A) (hM : 0 ≤ M) :
    0 ≤ cpMatrixFunctionalLinear φ M := by
  let Y := matrixLinearMap φ M
  have hY : 0 ≤ Y := matrixLinearMap_nonneg hφ hM
  have hpos := matrix_quadratic_nonneg Y hY (fun i => matrixUnit i p)
  have hcorner := cstarMatrix_diagonal_nonneg _ hpos p
  change 0 ≤ (∑ i, ∑ j, star (matrixUnit i p) * Y i j * matrixUnit j p) p p at hcorner
  simpa only [sum_cstarMatrix_apply, matrixUnit_corner_product, Y,
    matrixLinearMap_apply, cpMatrixFunctionalLinear_apply] using hcorner

def cpMatrixFunctional (p : Fin n)
    (φ : A →L[ℂ] CStarMatrix (Fin n) (Fin n) ℂ) (hφ : CompletelyPositive φ) :
    CStarMatrix (Fin n) (Fin n) A →ₚ[ℂ] ℂ :=
  PositiveLinearMap.mk₀ (cpMatrixFunctionalLinear φ) (cpMatrixFunctionalLinear_nonneg p φ hφ)

@[simp] lemma cpMatrixFunctional_apply (p : Fin n)
    (φ : A →L[ℂ] CStarMatrix (Fin n) (Fin n) ℂ) (hφ : CompletelyPositive φ)
    (M : CStarMatrix (Fin n) (Fin n) A) :
    cpMatrixFunctional p φ hφ M = ∑ i, ∑ j, φ (M i j) i j := rfl

end WeakPureInfiniteness

end

end OAI
