import OAI.Analysis.Pureness.Tensor.ScalarMatrixTensorFaithful
import OAI.Analysis.Pureness.Tensor.CommutingTensorClosure

namespace OAI
noncomputable section
namespace CuntzPureness
open CuntzTrace OrderedSemigroup Filter
open scoped TensorProduct
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A] [Nontrivial A]
variable (hsimple : TopologicallySimple A) (y : finiteCuntzSubmonoid (A := A))
variable (hy : y ≠ 0) (f : StateSpace y) (U : Ultrafilter ℕ)

abbrev MatrixStateScalarTensorCompletion :=
  commutingTensorClosure (matrixStateDiagonalAWEmbedding hsimple y hy f U)
    (scalarTracialMatrixAWEmbedding hsimple y hy f U)
    (scalarTracialMatrixAWEmbedding_commute hsimple y hy f U)

def matrixStateScalarTensorCompletionMap :
    A ⊗[ℂ] ScalarTracialMatrixUltraproduct U →⋆ₐ[ℂ]
      MatrixStateScalarTensorCompletion hsimple y hy f U :=
  commutingTensorClosureMap _ _ _

lemma matrixStateScalarTensorCompletionMap_injective :
    Function.Injective (matrixStateScalarTensorCompletionMap hsimple y hy f U) :=
  commutingTensorClosureMap_injective _ _ _ hsimple
    (scalarTracialMatrixAWEmbedding_injective hsimple y hy f U)

lemma matrixStateScalarTensorCompletionMap_dense :
    DenseRange (matrixStateScalarTensorCompletionMap hsimple y hy f U) :=
  commutingTensorClosureMap_denseRange _ _ _

def matrixStateScalarCompletionAWEmbedding :
    MatrixStateScalarTensorCompletion hsimple y hy f U →⋆ₐ[ℂ]
      NormalizedMatrixStateUltraAW hsimple y hy f U :=
  (MatrixStateScalarTensorCompletion hsimple y hy f U).subtype

lemma matrixStateScalarCompletionAWEmbedding_isometry :
    Isometry (matrixStateScalarCompletionAWEmbedding hsimple y hy f U) :=
  isometry_subtype_coe

lemma matrixStateScalarCompletionAWEmbedding_tensor
    (z : A ⊗[ℂ] ScalarTracialMatrixUltraproduct U) :
    matrixStateScalarCompletionAWEmbedding hsimple y hy f U
      (matrixStateScalarTensorCompletionMap hsimple y hy f U z) =
        matrixStateScalarTensorHom hsimple y hy f U z := rfl

lemma matrixStateScalarCompletion_value_left (a : A) :
    ultralimitAWQuasitrace (normalizedMatrixStatePositiveQuasitrace hsimple y hy f) U
      (normalizedMatrixStatePositiveQuasitrace_unit hsimple y hy f)
      (normalizedMatrixStatePositiveQuasitrace_metricSize_add hsimple y hy f)
      (normalizedMatrixStatePositiveQuasitrace_sqrt_add hsimple y hy f)
      (matrixStateScalarCompletionAWEmbedding hsimple y hy f U
        (matrixStateScalarTensorCompletionMap hsimple y hy f U (a ⊗ₜ[ℂ] 1))) =
      (normalizedRegularizedStateTwoQuasitrace hsimple y hy f).base a := by
  have he : matrixStateScalarCompletionAWEmbedding hsimple y hy f U
      (matrixStateScalarTensorCompletionMap hsimple y hy f U (a ⊗ₜ[ℂ] 1)) =
        matrixStateDiagonalAWEmbedding hsimple y hy f U a := by
    change matrixStateDiagonalAWEmbedding hsimple y hy f U a *
      scalarTracialMatrixAWEmbedding hsimple y hy f U 1 = _
    exact (congrArg (fun t => matrixStateDiagonalAWEmbedding hsimple y hy f U a * t)
      (scalarTracialMatrixAWEmbedding hsimple y hy f U).map_one').trans (mul_one _)
  rw [he]
  exact matrixStateDiagonalAWEmbedding_value hsimple y hy f U a

lemma matrixStateScalarCompletion_value_right (b : ScalarTracialMatrixUltraproduct U) :
    ultralimitAWQuasitrace (normalizedMatrixStatePositiveQuasitrace hsimple y hy f) U
      (normalizedMatrixStatePositiveQuasitrace_unit hsimple y hy f)
      (normalizedMatrixStatePositiveQuasitrace_metricSize_add hsimple y hy f)
      (normalizedMatrixStatePositiveQuasitrace_sqrt_add hsimple y hy f)
      (matrixStateScalarCompletionAWEmbedding hsimple y hy f U
        (matrixStateScalarTensorCompletionMap hsimple y hy f U (1 ⊗ₜ[ℂ] b))) =
      (scalarMatrixUltraTracialState U).functional b := by
  have he : matrixStateScalarCompletionAWEmbedding hsimple y hy f U
      (matrixStateScalarTensorCompletionMap hsimple y hy f U (1 ⊗ₜ[ℂ] b)) =
        scalarTracialMatrixAWEmbedding hsimple y hy f U b := by
    change matrixStateDiagonalAWEmbedding hsimple y hy f U 1 *
      scalarTracialMatrixAWEmbedding hsimple y hy f U b = _
    exact (congrArg (fun t => t * scalarTracialMatrixAWEmbedding hsimple y hy f U b)
      (matrixStateDiagonalAWEmbedding hsimple y hy f U).map_one').trans (one_mul _)
  rw [he]
  exact scalarTracialMatrixAWEmbedding_value hsimple y hy f U b
end CuntzPureness

end

end OAI
