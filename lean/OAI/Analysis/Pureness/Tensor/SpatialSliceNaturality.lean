import OAI.Analysis.Pureness.Tensor.SpatialVectorSlice
import OAI.Analysis.Pureness.Tensor.SpatialTensorQuotient

namespace OAI
noncomputable section
namespace CuntzPureness
open scoped TensorProduct CStarAlgebra
variable {A B C H K L : Type*}
variable [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
variable [CStarAlgebra C]
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
variable [NormedAddCommGroup L] [InnerProductSpace ℂ L] [CompleteSpace L]
variable (q : A →⋆ₐ[ℂ] C)
variable (α : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (β : B →⋆ₐ[ℂ] (K →L[ℂ] K))
variable (γ : C →⋆ₐ[ℂ] (L →L[ℂ] L))
variable (hα : Function.Injective α) (hβ : Function.Injective β) (hγ : Function.Injective γ)

omit [PartialOrder A] [StarOrderedRing A] [PartialOrder B] [StarOrderedRing B] in
lemma algebraicSpatialSlice_map (v w : K) (z : A ⊗[ℂ] B) :
    q (algebraicSpatialSlice β v w z) =
      algebraicSpatialSlice β v w (algebraicStarTensorMap q (StarAlgHom.id ℂ B) z) := by
  induction z using TensorProduct.inductionOn with
  | add x y hx hy => simpa using congrArg₂ (· + ·) hx hy
  | tmul a b => exact map_smul q _ a

include hγ in

theorem spatialVectorSlice_quotient (v w : K) (x : representedSpatialTensor α β) :
    q (spatialVectorSlice α β v w x) =
      spatialVectorSlice γ β v w (spatialTensorQuotientMap q α β γ hα hβ x) := by
  refine (representedSpatialTensor_dense α β).induction_on x ?_ ?_
  · apply isClosed_eq <;> fun_prop
  · intro z
    rw [spatialVectorSlice_tensor α hα, spatialTensorQuotientMap_tensor,
      spatialVectorSlice_tensor γ hγ]
    exact algebraicSpatialSlice_map q β v w z

include hγ in

theorem spatialVectorSlice_mem_kernel (v w : K) (x : representedSpatialTensor α β)
    (hx : spatialTensorQuotientMap q α β γ hα hβ x = 0) :
    spatialVectorSlice α β v w x ∈ q.toLinearMap.ker := by
  change q (spatialVectorSlice α β v w x) = 0
  rw [spatialVectorSlice_quotient q α β γ hα hβ hγ, hx, map_zero]
end CuntzPureness

end

end OAI
