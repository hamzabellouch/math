import OAI.Analysis.Pureness.GroupAlgebra.ReducedFreeGroupUltraEmbedding
import OAI.Analysis.Pureness.States.OriginalScalarNuclearQuasitrace

namespace OAI
noncomputable section
namespace CuntzPureness
open CuntzTrace OrderedSemigroup
open scoped TensorProduct
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A] [Nontrivial A]
variable (hsimple : TopologicallySimple A)
variable (y : finiteCuntzSubmonoid (A := A)) (hy : y ≠ 0) (f : StateSpace y)

def reducedFreeGroupAWEmbedding : ReducedFreeGroup →⋆ₐ[ℂ]
    NormalizedMatrixStateUltraAW hsimple y hy f freeGroupScalarUltrafilter :=
  (scalarTracialMatrixAWEmbedding hsimple y hy f freeGroupScalarUltrafilter).comp
    reducedFreeGroupUltraEmbedding

lemma reducedFreeGroupAWEmbedding_injective :
    Function.Injective (reducedFreeGroupAWEmbedding hsimple y hy f) :=
  (scalarTracialMatrixAWEmbedding_injective hsimple y hy f freeGroupScalarUltrafilter).comp
    reducedFreeGroupUltraEmbedding_injective

lemma reducedFreeGroupAWEmbedding_isometry :
    Isometry (reducedFreeGroupAWEmbedding hsimple y hy f) :=
  NonUnitalStarAlgHom.isometry (reducedFreeGroupAWEmbedding hsimple y hy f).toNonUnitalStarAlgHom
    (reducedFreeGroupAWEmbedding_injective hsimple y hy f)

lemma reducedFreeGroupAWEmbedding_commute (a : A) (b : ReducedFreeGroup) :
    Commute (matrixStateDiagonalAWEmbedding hsimple y hy f freeGroupScalarUltrafilter a)
      (reducedFreeGroupAWEmbedding hsimple y hy f b) :=
  scalarTracialMatrixAWEmbedding_commute hsimple y hy f freeGroupScalarUltrafilter a
    (reducedFreeGroupUltraEmbedding b)

lemma reducedFreeGroupAWEmbedding_value (b : ReducedFreeGroup) :
    matrixStateAWQuasitrace hsimple y hy f freeGroupScalarUltrafilter
      (reducedFreeGroupAWEmbedding hsimple y hy f b) =
        (reducedGroupTracialState (FreeGroup ℕ)).functional b :=
  (scalarTracialMatrixAWEmbedding_value hsimple y hy f freeGroupScalarUltrafilter
    (reducedFreeGroupUltraEmbedding b)).trans (reducedFreeGroupUltraEmbedding_trace b)

def originalFreeGroupTensorHom : A ⊗[ℂ] ReducedFreeGroup →⋆ₐ[ℂ]
    NormalizedMatrixStateUltraAW hsimple y hy f freeGroupScalarUltrafilter :=
  commutingStarTensorHom
    (matrixStateDiagonalAWEmbedding hsimple y hy f freeGroupScalarUltrafilter)
    (reducedFreeGroupAWEmbedding hsimple y hy f)
    (reducedFreeGroupAWEmbedding_commute hsimple y hy f)

lemma originalFreeGroupTensorHom_injective :
    Function.Injective (originalFreeGroupTensorHom hsimple y hy f) :=
  commutingStarTensorHom_injective hsimple _ _
    (reducedFreeGroupAWEmbedding_injective hsimple y hy f)
    (reducedFreeGroupAWEmbedding_commute hsimple y hy f)

lemma originalFreeGroupTensorHom_left (a : A) :
    originalFreeGroupTensorHom hsimple y hy f (a ⊗ₜ[ℂ] 1) =
      matrixStateDiagonalAWEmbedding hsimple y hy f freeGroupScalarUltrafilter a := by
  change matrixStateDiagonalAWEmbedding hsimple y hy f freeGroupScalarUltrafilter a *
    reducedFreeGroupAWEmbedding hsimple y hy f 1 = _
  exact (congrArg (fun t => matrixStateDiagonalAWEmbedding hsimple y hy f freeGroupScalarUltrafilter a * t)
    (reducedFreeGroupAWEmbedding hsimple y hy f).map_one).trans (mul_one _)

lemma originalFreeGroupTensorHom_right (b : ReducedFreeGroup) :
    originalFreeGroupTensorHom hsimple y hy f (1 ⊗ₜ[ℂ] b) =
      reducedFreeGroupAWEmbedding hsimple y hy f b := by
  change matrixStateDiagonalAWEmbedding hsimple y hy f freeGroupScalarUltrafilter 1 *
    reducedFreeGroupAWEmbedding hsimple y hy f b = _
  exact (congrArg (fun t => t * reducedFreeGroupAWEmbedding hsimple y hy f b)
    (matrixStateDiagonalAWEmbedding hsimple y hy f freeGroupScalarUltrafilter).map_one).trans (one_mul _)
end CuntzPureness

end

end OAI
