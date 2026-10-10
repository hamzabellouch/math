import Mathlib
import OAI.Analysis.WeakInfiniteness.CuntzComparison
import OAI.Analysis.WeakInfiniteness.MatrixHilbert
import OAI.Analysis.WeakInfiniteness.MatrixMaps

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal
open scoped TensorProduct ComplexConjugate
open scoped ENNReal InnerProductSpace
open scoped InnerProductSpace
open scoped TensorProduct InnerProductSpace
open Filter Topology
open Complex selfAdjoint
open scoped ComplexOrder

namespace WeakPureInfiniteness

noncomputable section

open scoped InnerProductSpace CStarAlgebra ComplexOrder

variable {A : Type*} [NonUnitalCStarAlgebra A]

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable {m n k : Type*} [Fintype m] [Fintype n] [Fintype k]

def rectangularRepresentation (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (M : CStarMatrix m n A) :
    HilbertVector n H →L[ℂ] HilbertVector m H := matrixAction (rectangularMap π M)

omit [Fintype m] in
@[simp] lemma rectangularRepresentation_apply (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H))
    (M : CStarMatrix m n A) (x : HilbertVector n H) (i : m) :
    rectangularRepresentation π M x i = ∑ j, π (M i j) (x j) := by
  simp [rectangularRepresentation, matrixAction_apply]

lemma rectangularRepresentation_square (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (M : CStarMatrix n n A) :
    rectangularRepresentation π M=matrixRepresentation π n M := rfl

omit [Fintype m] in
lemma rectangularRepresentation_mul (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H))
    (M : CStarMatrix m n A) (N : CStarMatrix n k A) :
    rectangularRepresentation π (M*N)=(rectangularRepresentation π M).comp (rectangularRepresentation π N) := by
  rw [rectangularRepresentation, rectangularMap_mul, matrixAction_mul]
  rfl

lemma rectangularRepresentation_star (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (M : CStarMatrix m n A) :
    rectangularRepresentation π M.conjTranspose=(rectangularRepresentation π M).adjoint := by
  rw [rectangularRepresentation, rectangularMap_star, matrixAction_star]
  rfl

omit [CompleteSpace H] in
def vectorTensorLinear (ξ : H) : HilbertVector n ℂ →ₗ[ℂ] HilbertVector n H where
  toFun x := WithLp.toLp 2 (fun i => x i • ξ)
  map_add' x y := by ext i; simp [add_smul]
  map_smul' c x := by ext i; simp [smul_smul]

omit [CompleteSpace H] in
def vectorTensorIsometry (ξ : H) (hξ : ‖ξ‖=1) : HilbertVector n ℂ →ₗᵢ[ℂ] HilbertVector n H where
  toLinearMap := vectorTensorLinear ξ
  norm_map' x := by
    have he : ‖vectorTensorLinear (n := n) ξ x‖^2=‖x‖^2 := by
      simp only [PiLp.norm_sq_eq_of_L2, vectorTensorLinear, LinearMap.coe_mk, AddHom.coe_mk,
        norm_smul, hξ, mul_one]
    nlinarith [norm_nonneg (vectorTensorLinear (n := n) ξ x), norm_nonneg x]

omit [CompleteSpace H] in
@[simp] lemma vectorTensorIsometry_apply (ξ : H) (hξ : ‖ξ‖=1) (x : HilbertVector n ℂ) (i : n) :
    vectorTensorIsometry ξ hξ x i = x i • ξ := rfl

def scalarMatrixAction (D : CStarMatrix m n ℂ) : HilbertVector n H →L[ℂ] HilbertVector m H :=
  rectangularRepresentation (StarAlgHom.ofId ℂ (H →L[ℂ] H)).toNonUnitalStarAlgHom D

omit [Fintype m] in
@[simp] lemma scalarMatrixAction_apply (D : CStarMatrix m n ℂ) (x : HilbertVector n H) (i : m) :
    scalarMatrixAction D x i = ∑ j, D i j • x j := by
  simp [scalarMatrixAction, Algebra.algebraMap_eq_smul_one]

lemma scalarMatrixAction_star (D : CStarMatrix m n ℂ) :
    scalarMatrixAction (H := H) D.conjTranspose=(scalarMatrixAction (H := H) D).adjoint :=
  rectangularRepresentation_star _ _

omit [Fintype m] in
lemma rectangularRepresentation_scalarRight (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H))
    (L : CStarMatrix m n A) (D : CStarMatrix n k ℂ) :
    rectangularRepresentation π (matrixScalarRight L D)=
      (rectangularRepresentation π L).comp (scalarMatrixAction (H := H) D) := by
  ext x i
  simp only [rectangularRepresentation_apply, matrixScalarRight_apply, map_sum, map_smul,
    sum_apply, smul_apply, ContinuousLinearMap.comp_apply,
    scalarMatrixAction_apply]
  rw [Finset.sum_comm]

lemma scalarAction_vectorTensor (D : CStarMatrix n n ℂ) (ξ : H) (hξ : ‖ξ‖=1) :
    (scalarMatrixAction (H := H) D).comp (vectorTensorIsometry (n := n) ξ hξ).toContinuousLinearMap =
      (vectorTensorIsometry ξ hξ).toContinuousLinearMap.comp (scalarMatrixAction (H := ℂ) D) := by
  ext x i
  simp only [ContinuousLinearMap.comp_apply, LinearIsometry.coe_toContinuousLinearMap,
    scalarMatrixAction_apply, vectorTensorIsometry_apply, Finset.sum_smul,
    smul_smul, smul_eq_mul]

lemma diagonal_rep_plateau (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H))
    (e : A) (ξ : H) (hξ : ‖ξ‖=1) (he : π e ξ=ξ) (d : ℕ) :
    (matrixRepresentation π (Fin d) (diagonalCopies d e)).comp
      (vectorTensorIsometry ξ hξ).toContinuousLinearMap = (vectorTensorIsometry ξ hξ).toContinuousLinearMap := by
  ext x i
  simp [matrixRepresentation_apply, diagonalCopies, Matrix.diagonal_apply, apply_ite, ite_apply, he]

end

end WeakPureInfiniteness
end

end OAI
