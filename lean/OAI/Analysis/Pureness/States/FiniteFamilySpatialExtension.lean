import OAI.Analysis.Pureness.States.FiniteFamilyNuclearSpatial
import OAI.Analysis.Pureness.States.FiniteFamilyAWPositive
import OAI.Analysis.Pureness.States.RegularizedStateSpatialTransport
import OAI.Analysis.Pureness.Tensor.CauchySpatialFaithful

namespace OAI
noncomputable section
namespace CuntzPureness.CompatibleFiniteQuasitrace
open CuntzTrace
open scoped TensorProduct NNReal ENNReal
universe u
variable {A : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A] [Nontrivial A]
variable (F : CompatibleFiniteQuasitrace A)
variable (hmono : ∀ n, Monotone (fun a : Positive (FinMatrix A n) => (F.level n a.1).re))
variable (hF : F.level 1 1=1)
variable (hsimple : TopologicallySimple A) (hA : IsNuclear.{u,0} A)

def finOneOriginalSpatialAW :
    representedSpatialTensor (finOneOriginalGNS (A := A)) (reducedGroupAlgebra (FreeGroup ℕ)).subtype →⋆ₐ[ℂ]
      F.MatrixUltraAW hmono hF freeGroupScalarUltrafilter :=
  (F.originalFreeGroupSpatialAWEmbedding hmono hF hsimple hA).comp
    (spatialTensorQuotientMap scalarFinOneEquiv.symm.toStarAlgHom
      (finOneOriginalGNS (A := A)) (reducedGroupAlgebra (FreeGroup ℕ)).subtype
      (simpleStateGNS A) (finOneOriginalGNS_injective hsimple) Subtype.val_injective)

lemma finOneOriginalSpatialAW_tensor (M : FinMatrix A 1) (b : ReducedFreeGroup) :
    finOneOriginalSpatialAW F hmono hF hsimple hA
      (spatialCompletionMap (finOneOriginalGNS (A := A))
        (reducedGroupAlgebra (FreeGroup ℕ)).subtype (M ⊗ₜ[ℂ] b)) =
      F.matrixFinOneAW hmono hF freeGroupScalarUltrafilter M *
        F.reducedFreeGroupAWEmbedding hmono hF b := by
  have he := spatialTensorQuotientMap_tensor scalarFinOneEquiv.symm.toStarAlgHom
    (finOneOriginalGNS (A := A)) (reducedGroupAlgebra (FreeGroup ℕ)).subtype
    (simpleStateGNS A) (finOneOriginalGNS_injective hsimple) Subtype.val_injective (M ⊗ₜ[ℂ] b)
  exact (congrArg (F.originalFreeGroupSpatialAWEmbedding hmono hF hsimple hA) he).trans
    (F.originalFreeGroupSpatialAWEmbedding_tensor hmono hF hsimple hA (scalarFinOneEquiv.symm M ⊗ₜ[ℂ] b))

local instance matrixAmbientNontrivial : Nontrivial
    ((F.matrixUltralimitPositive hmono hF freeGroupScalarUltrafilter).CauchyQuotient
      (F.matrixUltralimitTriangle hmono hF freeGroupScalarUltrafilter)) :=
  F.matrixUltraAWNontrivial hmono hF freeGroupScalarUltrafilter

abbrev ExtendedAW :=
  (F.matrixAWPositive hmono hF freeGroupScalarUltrafilter).CauchyQuotient
    (F.matrixAWPositive_triangle hmono hF freeGroupScalarUltrafilter)

def spatialExtension :
    (F.positiveLevel hmono 1).CauchyFreeGroupTensorTarget
      (F.positiveLevel_metricSize_add hmono 1) →⋆ₐ[ℂ]
        ExtendedAW F hmono hF :=
  (F.positiveLevel hmono 1).cauchySpatialExtension
    (F.matrixAWPositive hmono hF freeGroupScalarUltrafilter)
    (F.positiveLevel_metricSize_add hmono 1)
    (F.matrixAWPositive_triangle hmono hF freeGroupScalarUltrafilter)
    ((F.positiveLevel hmono 1).cauchySourceGNS
      (F.positiveLevel_metricSize_add hmono 1))
    (finOneOriginalGNS (A := A))
    ((F.positiveLevel hmono 1).cauchySourceGNS_injective
      (F.positiveLevel_metricSize_add hmono 1))
    (finOneOriginalSpatialAW F hmono hF hsimple hA)
    (F.matrixFinOneAW hmono hF freeGroupScalarUltrafilter)
    (F.reducedFreeGroupAWEmbedding hmono hF)
    (finOneOriginalSpatialAW_tensor F hmono hF hsimple hA)
    ((1 : ℝ≥0))
    (F.matrixFinOneAW_positive hmono hF freeGroupScalarUltrafilter)
    ((F.positiveLevel hmono 1).cauchyTargetGNS
      (F.positiveLevel_metricSize_add hmono 1))
    ((F.positiveLevel hmono 1).cauchyTargetGNS_injective
      (F.positiveLevel_metricSize_add hmono 1))

lemma spatialExtension_injective : Function.Injective (F.spatialExtension hmono hF hsimple hA) :=
  (F.positiveLevel hmono 1).cauchySpatialExtension_injective
    (F.matrixAWPositive hmono hF freeGroupScalarUltrafilter)
    (F.positiveLevel_metricSize_add hmono 1)
    (F.matrixAWPositive_triangle hmono hF freeGroupScalarUltrafilter)
    ((F.positiveLevel hmono 1).cauchySourceGNS
      (F.positiveLevel_metricSize_add hmono 1))
    (finOneOriginalGNS (A := A))
    ((F.positiveLevel hmono 1).cauchySourceGNS_injective
      (F.positiveLevel_metricSize_add hmono 1))
    (finOneOriginalSpatialAW F hmono hF hsimple hA)
    (F.matrixFinOneAW hmono hF freeGroupScalarUltrafilter)
    (F.reducedFreeGroupAWEmbedding hmono hF)
    (finOneOriginalSpatialAW_tensor F hmono hF hsimple hA)
    ((1 : ℝ≥0))
    (F.matrixFinOneAW_positive hmono hF freeGroupScalarUltrafilter)
    ((F.positiveLevel hmono 1).cauchyTargetGNS
      (F.positiveLevel_metricSize_add hmono 1))
    ((F.positiveLevel hmono 1).cauchyTargetGNS_injective
      (F.positiveLevel_metricSize_add hmono 1)) (by norm_num : (0 : ℝ≥0) < 1)

lemma extendedAW_finite (x : F.ExtendedAW hmono hF) (hx : star x*x=1) : x*star x=1 :=
  PositiveQuasitrace.cauchyQuotient_isometry_unitary _ _
    (F.matrixAWPositive_sqrt hmono hF freeGroupScalarUltrafilter) x hx

include hF hsimple hA in
lemma spatialTensor_finite
    (x : (F.positiveLevel hmono 1).CauchyFreeGroupTensorTarget (F.positiveLevel_metricSize_add hmono 1))
    (hx : star x*x=1) : x*star x=1 := by
  let Φ := F.spatialExtension hmono hF hsimple hA
  have hs : Φ (star x*x)=star (Φ x)*Φ x :=
    (map_mul Φ (star x) x).trans (congrArg (fun v => v*Φ x) (map_star Φ x))
  have ht := F.extendedAW_finite hmono hF (Φ x) (hs.symm.trans ((congrArg Φ hx).trans (map_one Φ)))
  apply F.spatialExtension_injective hmono hF hsimple hA
  exact (map_mul Φ x (star x)).trans
    ((congrArg (fun v => Φ x*v) (map_star Φ x)).trans (ht.trans (map_one Φ).symm))
end CuntzPureness.CompatibleFiniteQuasitrace

end

end OAI
