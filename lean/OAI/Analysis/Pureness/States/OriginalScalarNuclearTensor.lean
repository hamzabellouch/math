import OAI.Analysis.Pureness.Tensor.NuclearSpatialTensor
import OAI.Analysis.Pureness.Tensor.OriginalScalarSpatialTensor
import OAI.Analysis.Pureness.Tensor.ScalarMatrixTensorCompletion

namespace OAI
noncomputable section
namespace CuntzPureness
open CuntzTrace OrderedSemigroup
open scoped TensorProduct
universe u
variable {A : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A] [Nontrivial A]
variable (hsimple : TopologicallySimple A) (hA : IsNuclear.{u, 0} A)
variable (y : finiteCuntzSubmonoid (A := A)) (hy : y ≠ 0) (f : StateSpace y)
variable (U : Ultrafilter ℕ)

include hA in

theorem originalScalarSpatialHom_norm_eq_AW (z : A ⊗[ℂ] ScalarTracialMatrixUltraproduct U) :
    ‖originalScalarSpatialHom A U z‖ = ‖matrixStateScalarTensorHom hsimple y hy f U z‖ :=
  hA.faithful_tensor_norm_eq _ _ (originalScalarSpatialHom_injective A U hsimple)
    (matrixStateScalarTensorHom_injective hsimple y hy f U) z

def originalScalarNuclearEquiv : OriginalScalarSpatialCompletion A U ≃⋆ₐ[ℂ]
    MatrixStateScalarTensorCompletion hsimple y hy f U :=
  hA.tensorCompletionEquiv (originalScalarSpatialCompletionMap A U)
    (matrixStateScalarTensorCompletionMap hsimple y hy f U)
    (originalScalarSpatialCompletionMap_injective A U hsimple)
    (matrixStateScalarTensorCompletionMap_injective hsimple y hy f U)
    (originalScalarSpatialCompletionMap_dense A U)
    (matrixStateScalarTensorCompletionMap_dense hsimple y hy f U)

lemma originalScalarNuclearEquiv_tensor (z : A ⊗[ℂ] ScalarTracialMatrixUltraproduct U) :
    originalScalarNuclearEquiv hsimple hA y hy f U (originalScalarSpatialCompletionMap A U z) =
      matrixStateScalarTensorCompletionMap hsimple y hy f U z :=
  hA.tensorCompletionEquiv_tensor _ _ _ _ _ _ z

lemma originalScalarNuclearEquiv_norm (x : OriginalScalarSpatialCompletion A U) :
    ‖originalScalarNuclearEquiv hsimple hA y hy f U x‖ = ‖x‖ :=
  hA.tensorCompletionEquiv_norm _ _ _ _ _ _ x

def originalScalarSpatialAWEmbedding : OriginalScalarSpatialCompletion A U →⋆ₐ[ℂ]
    NormalizedMatrixStateUltraAW hsimple y hy f U :=
  (matrixStateScalarCompletionAWEmbedding hsimple y hy f U).comp
    (originalScalarNuclearEquiv hsimple hA y hy f U).toStarAlgHom

lemma originalScalarSpatialAWEmbedding_tensor (z : A ⊗[ℂ] ScalarTracialMatrixUltraproduct U) :
    originalScalarSpatialAWEmbedding hsimple hA y hy f U
      (originalScalarSpatialCompletionMap A U z) = matrixStateScalarTensorHom hsimple y hy f U z := by
  exact congrArg (matrixStateScalarCompletionAWEmbedding hsimple y hy f U)
    (originalScalarNuclearEquiv_tensor hsimple hA y hy f U z)

lemma originalScalarSpatialAWEmbedding_isometry :
    Isometry (originalScalarSpatialAWEmbedding hsimple hA y hy f U) := by
  apply AddMonoidHomClass.isometry_of_norm
  intro x
  exact originalScalarNuclearEquiv_norm hsimple hA y hy f U x

lemma originalScalarSpatialAWEmbedding_left (a : A) :
    originalScalarSpatialAWEmbedding hsimple hA y hy f U
      (originalScalarSpatialCompletionMap A U (a ⊗ₜ[ℂ] 1)) =
        matrixStateDiagonalAWEmbedding hsimple y hy f U a := by
  exact (originalScalarSpatialAWEmbedding_tensor hsimple hA y hy f U _).trans
    (by
      change matrixStateDiagonalAWEmbedding hsimple y hy f U a *
        scalarTracialMatrixAWEmbedding hsimple y hy f U 1 = _
      exact (congrArg (fun t => matrixStateDiagonalAWEmbedding hsimple y hy f U a * t)
        (scalarTracialMatrixAWEmbedding hsimple y hy f U).map_one).trans (mul_one _))

lemma originalScalarSpatialAWEmbedding_right (b : ScalarTracialMatrixUltraproduct U) :
    originalScalarSpatialAWEmbedding hsimple hA y hy f U
      (originalScalarSpatialCompletionMap A U (1 ⊗ₜ[ℂ] b)) =
        scalarTracialMatrixAWEmbedding hsimple y hy f U b := by
  exact (originalScalarSpatialAWEmbedding_tensor hsimple hA y hy f U _).trans
    (by
      change matrixStateDiagonalAWEmbedding hsimple y hy f U 1 *
        scalarTracialMatrixAWEmbedding hsimple y hy f U b = _
      exact (congrArg (fun t => t * scalarTracialMatrixAWEmbedding hsimple y hy f U b)
        (matrixStateDiagonalAWEmbedding hsimple y hy f U).map_one).trans (one_mul _))
end CuntzPureness

end

end OAI
