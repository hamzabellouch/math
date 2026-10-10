import OAI.Analysis.BoundedHochschild.CompletelyPositiveCompression
import OAI.Analysis.BoundedHochschild.MatrixScalarColumns
import OAI.Analysis.Naimark.Basic

namespace OAI

/-! A positive functional on a matrix algebra gives a completely positive
map into the corresponding finite-dimensional operator algebra. -/

noncomputable section

open scoped ComplexOrder InnerProductSpace

namespace BoundedHochschild.KadisonRingrose

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

def singleCStarMatrix {n : ℕ} (i j : Fin n) (a : A) : CStarMatrix (Fin n) (Fin n) A :=
  CStarMatrix.ofMatrix (Matrix.single i j a)

omit [PartialOrder A] [StarOrderedRing A] in
lemma singleCStarMatrix_star {n : ℕ} (i j : Fin n) (a : A) :
    star (singleCStarMatrix i j a) = singleCStarMatrix j i (star a) :=
  congrArg CStarMatrix.ofMatrix (Matrix.conjTranspose_single i j a)

omit [PartialOrder A] [StarOrderedRing A] in
lemma singleCStarMatrix_diagonal {n : ℕ} (i₀ i j : Fin n) (a : A) :
    star (singleCStarMatrix i₀ i (1 : A)) *
      (matrixScalarHom n a * singleCStarMatrix i₀ j 1) = singleCStarMatrix i j a := by
  rw [singleCStarMatrix_star, star_one, ← mul_assoc]
  change CStarMatrix.ofMatrix
    (Matrix.single i i₀ 1 * Matrix.scalar (Fin n) a * Matrix.single i₀ j 1) = _
  rw [Matrix.single_mul_mul_single]
  simp only [Matrix.scalar_apply, Matrix.diagonal_apply_eq, one_mul, mul_one]
  rfl

def matrixFunctionalVector {n : ℕ} (F : CStarMatrix (Fin n) (Fin n) A →ₚ[ℂ] ℂ)
    (i₀ i : Fin n) : F.GNS :=
  F.gnsStarAlgHom (singleCStarMatrix i₀ i 1) (NaimarkZFC.gnsVector F)

def matrixFunctionalEmbedding {n : ℕ} (F : CStarMatrix (Fin n) (Fin n) A →ₚ[ℂ] ℂ)
    (i₀ : Fin n) : EuclideanSpace ℂ (Fin n) →L[ℂ] F.GNS :=
  LinearMap.toContinuousLinearMap
    { toFun := fun ξ => ∑ i, ξ i • matrixFunctionalVector F i₀ i
      map_add' := fun ξ η => by simp [add_smul, Finset.sum_add_distrib]
      map_smul' := fun z ξ => by simp [Finset.smul_sum, mul_smul] }

@[simp] lemma matrixFunctionalEmbedding_single {n : ℕ}
    (F : CStarMatrix (Fin n) (Fin n) A →ₚ[ℂ] ℂ) (i₀ i : Fin n) :
    matrixFunctionalEmbedding F i₀ (EuclideanSpace.single i 1) =
      matrixFunctionalVector F i₀ i := by
  change (∑ j, (EuclideanSpace.single i (1 : ℂ)) j • matrixFunctionalVector F i₀ j) = _
  simp [PiLp.single_apply]

def matrixFunctionalCP {n : ℕ} (F : CStarMatrix (Fin n) (Fin n) A →ₚ[ℂ] ℂ)
    (i₀ : Fin n) : CompletelyPositiveMap A
      (EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)) :=
  compressCompletelyPositive
    (CompletelyPositiveMapClass.toCompletelyPositiveLinearMap
      (F.gnsStarAlgHom.comp (matrixScalarHom n))) (matrixFunctionalEmbedding F i₀)

lemma matrixFunctionalCP_coefficient {n : ℕ}
    (F : CStarMatrix (Fin n) (Fin n) A →ₚ[ℂ] ℂ) (i₀ i j : Fin n) (a : A) :
    inner ℂ (EuclideanSpace.single i 1)
      (matrixFunctionalCP F i₀ a (EuclideanSpace.single j 1)) =
        F (singleCStarMatrix i j a) := by
  change inner ℂ (EuclideanSpace.single i 1)
    ((matrixFunctionalEmbedding F i₀).adjoint
      (F.gnsStarAlgHom (matrixScalarHom n a)
        (matrixFunctionalEmbedding F i₀ (EuclideanSpace.single j 1)))) = _
  rw [ContinuousLinearMap.adjoint_inner_right, matrixFunctionalEmbedding_single,
    matrixFunctionalEmbedding_single]
  unfold matrixFunctionalVector
  rw [← ContinuousLinearMap.adjoint_inner_right, ← ContinuousLinearMap.star_eq_adjoint,
    ← map_star]
  change inner ℂ (NaimarkZFC.gnsVector F)
    ((F.gnsStarAlgHom (star (singleCStarMatrix i₀ i 1)) *
      (F.gnsStarAlgHom (matrixScalarHom n a) *
        F.gnsStarAlgHom (singleCStarMatrix i₀ j 1))) (NaimarkZFC.gnsVector F)) = _
  rw [← map_mul, ← map_mul, NaimarkZFC.gnsVector_coefficient,
    singleCStarMatrix_diagonal]

end BoundedHochschild.KadisonRingrose

end

end OAI
