import OAI.Analysis.Pureness.Operators.FaithfulHilbertChoice
import OAI.Analysis.Pureness.Tensor.SpatialSliceNaturality

namespace OAI
noncomputable section
namespace CuntzPureness
open scoped TensorProduct
variable {A B C K : Type*}
variable [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
variable [CStarAlgebra C] [PartialOrder C] [StarOrderedRing C]
variable [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
variable (β : B →⋆ₐ[ℂ] (K →L[ℂ] K))

abbrev universalLeftSpatialTensor (A : Type*) [CStarAlgebra A]
    [PartialOrder A] [StarOrderedRing A] :=
  representedSpatialTensor (H := FaithfulHilbertSpace A) (faithfulHilbertRepresentation A) β

variable (q : A →⋆ₐ[ℂ] C) (hβ : Function.Injective β)

def universalLeftTensorQuotient :
    universalLeftSpatialTensor β A →⋆ₐ[ℂ] universalLeftSpatialTensor β C :=
  spatialTensorQuotientMap (H := FaithfulHilbertSpace A) (L := FaithfulHilbertSpace C) q (faithfulHilbertRepresentation A) β (faithfulHilbertRepresentation C)
    (faithfulHilbertRepresentation_injective A) hβ

lemma universalLeftTensorQuotient_surjective (hq : Function.Surjective q) :
    Function.Surjective (universalLeftTensorQuotient β q hβ) :=
  spatialTensorQuotientMap_surjective (H := FaithfulHilbertSpace A) (L := FaithfulHilbertSpace C) q (faithfulHilbertRepresentation A) β (faithfulHilbertRepresentation C)
    (faithfulHilbertRepresentation_injective A) hβ hq

lemma universalLeftTensorQuotient_tensor (a : A) (b : B) :
    universalLeftTensorQuotient β q hβ
      (spatialCompletionMap (H := FaithfulHilbertSpace A) (faithfulHilbertRepresentation A) β (a ⊗ₜ[ℂ] b)) =
    spatialCompletionMap (H := FaithfulHilbertSpace C) (faithfulHilbertRepresentation C) β (q a ⊗ₜ[ℂ] b) :=
  spatialTensorQuotientMap_tensor (H := FaithfulHilbertSpace A) (L := FaithfulHilbertSpace C) q (faithfulHilbertRepresentation A) β (faithfulHilbertRepresentation C)
    (faithfulHilbertRepresentation_injective A) hβ _

lemma universalLeftTensorQuotient_slice_kernel (v w : K)
    (x : universalLeftSpatialTensor β A)
    (hx : universalLeftTensorQuotient β q hβ x = 0) :
    q (spatialVectorSlice (H := FaithfulHilbertSpace A) (faithfulHilbertRepresentation A) β v w x) = 0 :=
  spatialVectorSlice_mem_kernel (H := FaithfulHilbertSpace A) (L := FaithfulHilbertSpace C) q (faithfulHilbertRepresentation A) β (faithfulHilbertRepresentation C)
    (faithfulHilbertRepresentation_injective A) hβ (faithfulHilbertRepresentation_injective C) v w x hx
end CuntzPureness

end

end OAI
