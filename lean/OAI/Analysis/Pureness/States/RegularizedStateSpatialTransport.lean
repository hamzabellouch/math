import OAI.Analysis.Pureness.Cuntz.MatrixStateAWPositive
import OAI.Analysis.Pureness.States.OriginalFreeGroupQuasitrace
import OAI.Analysis.Pureness.Tensor.CauchySpatialExtension

namespace OAI
noncomputable section
namespace CuntzPureness
open CuntzTrace OrderedSemigroup
open scoped TensorProduct NNReal ENNReal
universe u
variable {A : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A] [Nontrivial A]
variable (hsimple : TopologicallySimple A) (y : finiteCuntzSubmonoid (A := A))
variable (hy : y ≠ 0) (f : StateSpace y) (hA : IsNuclear.{u,0} A)

abbrev finOneOriginalGNS : FinMatrix A 1 →⋆ₐ[ℂ] (SimpleStateHilbert A →L[ℂ] SimpleStateHilbert A) :=
  (simpleStateGNS A).comp scalarFinOneEquiv.symm.toStarAlgHom

include hsimple in
lemma finOneOriginalGNS_injective : Function.Injective (finOneOriginalGNS (A := A)) :=
  (simpleStateGNS_injective A hsimple).comp scalarFinOneEquiv.symm.injective

def finOneOriginalSpatialAW :
    representedSpatialTensor (finOneOriginalGNS (A := A)) (reducedGroupAlgebra (FreeGroup ℕ)).subtype →⋆ₐ[ℂ]
      NormalizedMatrixStateUltraAW hsimple y hy f freeGroupScalarUltrafilter :=
  (originalFreeGroupSpatialAWEmbedding hsimple y hy f hA).comp
    (spatialTensorQuotientMap scalarFinOneEquiv.symm.toStarAlgHom
      (finOneOriginalGNS (A := A)) (reducedGroupAlgebra (FreeGroup ℕ)).subtype
      (simpleStateGNS A) (finOneOriginalGNS_injective hsimple) Subtype.val_injective)

lemma finOneOriginalSpatialAW_tensor (M : FinMatrix A 1) (b : ReducedFreeGroup) :
    finOneOriginalSpatialAW hsimple y hy f hA
      (spatialCompletionMap (finOneOriginalGNS (A := A))
        (reducedGroupAlgebra (FreeGroup ℕ)).subtype (M ⊗ₜ[ℂ] b)) =
      matrixStateFinOneAW hsimple y hy f freeGroupScalarUltrafilter M *
        reducedFreeGroupAWEmbedding hsimple y hy f b := by
  have he := spatialTensorQuotientMap_tensor scalarFinOneEquiv.symm.toStarAlgHom
    (finOneOriginalGNS (A := A)) (reducedGroupAlgebra (FreeGroup ℕ)).subtype
    (simpleStateGNS A) (finOneOriginalGNS_injective hsimple) Subtype.val_injective (M ⊗ₜ[ℂ] b)
  exact (congrArg (originalFreeGroupSpatialAWEmbedding hsimple y hy f hA) he).trans
    (originalFreeGroupSpatialAWEmbedding_tensor hsimple y hy f hA (scalarFinOneEquiv.symm M ⊗ₜ[ℂ] b))

abbrev RegularizedStateExtendedAW :=
  (matrixStateAWPositive hsimple y hy f freeGroupScalarUltrafilter).CauchyQuotient
    (matrixStateAWPositive_triangle hsimple y hy f freeGroupScalarUltrafilter)

def regularizedStateSpatialExtension :
    (regularizedStateCauchyPositive hsimple y hy f).CauchyFreeGroupTensorTarget
      (regularizedStateCauchyTriangle hsimple y hy f) →⋆ₐ[ℂ]
        RegularizedStateExtendedAW hsimple y hy f :=
  (regularizedStateCauchyPositive hsimple y hy f).cauchySpatialExtension
    (matrixStateAWPositive hsimple y hy f freeGroupScalarUltrafilter)
    (regularizedStateCauchyTriangle hsimple y hy f)
    (matrixStateAWPositive_triangle hsimple y hy f freeGroupScalarUltrafilter)
    ((regularizedStateCauchyPositive hsimple y hy f).cauchySourceGNS
      (regularizedStateCauchyTriangle hsimple y hy f))
    (finOneOriginalGNS (A := A))
    ((regularizedStateCauchyPositive hsimple y hy f).cauchySourceGNS_injective
      (regularizedStateCauchyTriangle hsimple y hy f))
    (finOneOriginalSpatialAW hsimple y hy f hA)
    (matrixStateFinOneAW hsimple y hy f freeGroupScalarUltrafilter)
    (reducedFreeGroupAWEmbedding hsimple y hy f)
    (finOneOriginalSpatialAW_tensor hsimple y hy f hA)
    (regularizedStateNormalization y f)
    (matrixStateFinOneAW_positive hsimple y hy f freeGroupScalarUltrafilter)
    ((regularizedStateCauchyPositive hsimple y hy f).cauchyTargetGNS
      (regularizedStateCauchyTriangle hsimple y hy f))
    ((regularizedStateCauchyPositive hsimple y hy f).cauchyTargetGNS_injective
      (regularizedStateCauchyTriangle hsimple y hy f))
end CuntzPureness

end

end OAI
