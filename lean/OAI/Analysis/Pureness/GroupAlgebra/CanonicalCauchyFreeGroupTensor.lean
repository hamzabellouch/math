import OAI.Analysis.Pureness.Tensor.UniversalLeftTensorQuotient
import OAI.Analysis.Pureness.GroupAlgebra.CauchyFreeGroupTensorQuotient

namespace OAI
namespace CuntzPureness.PositiveQuasitrace
open scoped TensorProduct
variable {D : Type*}
variable [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D] [Nontrivial D]
variable (T : CuntzPureness.PositiveQuasitrace D)
variable (ht : ∀ x y, T.metricSize (x+y) ≤ T.metricSize x+T.metricSize y)

noncomputable abbrev cauchySourceGNS := faithfulHilbertRepresentation (T.cauchySequenceAlgebra ht)
noncomputable abbrev cauchyTargetGNS := faithfulHilbertRepresentation (T.CauchyQuotient ht)

lemma cauchySourceGNS_injective : Function.Injective (T.cauchySourceGNS ht) :=
  faithfulHilbertRepresentation_injective (T.cauchySequenceAlgebra ht)

lemma cauchyTargetGNS_injective : Function.Injective (T.cauchyTargetGNS ht) :=
  faithfulHilbertRepresentation_injective (T.CauchyQuotient ht)

noncomputable abbrev CauchyFreeGroupTensorSource :=
  universalLeftSpatialTensor (K := GroupL2 (FreeGroup ℕ)) (reducedGroupAlgebra (FreeGroup ℕ)).subtype
    (T.cauchySequenceAlgebra ht)

noncomputable abbrev CauchyFreeGroupTensorTarget :=
  universalLeftSpatialTensor (K := GroupL2 (FreeGroup ℕ)) (reducedGroupAlgebra (FreeGroup ℕ)).subtype
    (T.CauchyQuotient ht)

noncomputable def canonicalCauchyFreeGroupTensorMap :=
  universalLeftTensorQuotient (K := GroupL2 (FreeGroup ℕ)) (reducedGroupAlgebra (FreeGroup ℕ)).subtype
    (T.cauchyQuotientStarHom ht) Subtype.val_injective

lemma canonicalCauchyFreeGroupTensorMap_surjective :
    Function.Surjective (T.canonicalCauchyFreeGroupTensorMap ht) :=
  universalLeftTensorQuotient_surjective (K := GroupL2 (FreeGroup ℕ)) (reducedGroupAlgebra (FreeGroup ℕ)).subtype
    (T.cauchyQuotientStarHom ht) Subtype.val_injective (T.cauchyQuotientMap_surjective ht)

lemma canonicalCauchyFreeGroupTensorMap_tensor (u : T.cauchySequenceAlgebra ht)
    (b : ReducedFreeGroup) :
    T.canonicalCauchyFreeGroupTensorMap ht
      (spatialCompletionMap (H := FaithfulHilbertSpace (T.cauchySequenceAlgebra ht))
        (T.cauchySourceGNS ht) (reducedGroupAlgebra (FreeGroup ℕ)).subtype (u ⊗ₜ[ℂ] b)) =
      spatialCompletionMap (H := FaithfulHilbertSpace (T.CauchyQuotient ht))
        (T.cauchyTargetGNS ht) (reducedGroupAlgebra (FreeGroup ℕ)).subtype
        (T.cauchyQuotientStarHom ht u ⊗ₜ[ℂ] b) :=
  universalLeftTensorQuotient_tensor (K := GroupL2 (FreeGroup ℕ)) (reducedGroupAlgebra (FreeGroup ℕ)).subtype
    (T.cauchyQuotientStarHom ht) Subtype.val_injective u b
end CuntzPureness.PositiveQuasitrace

end OAI
