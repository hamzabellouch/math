import OAI.Analysis.Pureness.Tensor.SpatialTensorQuotient
import OAI.Analysis.Pureness.Tensor.AlgebraicStarDescent
import OAI.Analysis.Pureness.Tensor.SpatialTensorFaithful

namespace OAI
noncomputable section
namespace CuntzPureness
open scoped TensorProduct CStarAlgebra
variable {A B C H K L : Type*}
variable [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B] [CStarAlgebra C]
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
variable [NormedAddCommGroup L] [InnerProductSpace ℂ L] [CompleteSpace L]
variable (q : A →⋆ₐ[ℂ] C) (hq : Function.Surjective q)
variable (α : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (β : B →⋆ₐ[ℂ] (K →L[ℂ] K))

omit [PartialOrder A] [StarOrderedRing A] [PartialOrder B] [StarOrderedRing B] in
lemma algebraicTensor_quotient_zero (z : A ⊗[ℂ] B)
    (hz : algebraicStarTensorMap q (StarAlgHom.id ℂ B) z = 0) :
    (spatialTensorKernelIdeal q α β).quotientStarHom (spatialCompletionMap α β z) = 0 := by
  apply Quotient.sound
  apply (denseKernelClosedIdeal_mem _ _ (representedSpatialTensor_dense α β) _).mpr
  change spatialCompletionMap α β z ∈
    (denseKernelImage (spatialCompletionMap α β)
      (algebraicStarTensorMap q (StarAlgHom.id ℂ B))).topologicalClosure
  exact Submodule.le_topologicalClosure _ ⟨z, hz, rfl⟩

def algebraicQuotientTensorLift : C ⊗[ℂ] B →⋆ₐ[ℂ] SpatialTensorIdealQuotient q α β :=
  algebraicStarDescent (algebraicStarTensorMap q (StarAlgHom.id ℂ B))
    (TensorProduct.map_surjective hq Function.surjective_id)
    ((spatialTensorKernelIdeal q α β).quotientStarHom.comp (spatialCompletionMap α β))
    (algebraicTensor_quotient_zero q α β)

omit [PartialOrder A] [StarOrderedRing A] [PartialOrder B] [StarOrderedRing B] in
lemma algebraicQuotientTensorLift_map (z : A ⊗[ℂ] B) :
    algebraicQuotientTensorLift q hq α β (algebraicStarTensorMap q (StarAlgHom.id ℂ B) z) =
      (spatialTensorKernelIdeal q α β).quotientStarHom (spatialCompletionMap α β z) :=
  algebraicStarDescent_apply _ _ _ _ z

omit [PartialOrder A] [StarOrderedRing A] [PartialOrder B] [StarOrderedRing B] in
lemma algebraicQuotientTensorLift_dense : DenseRange (algebraicQuotientTensorLift q hq α β) := by
  have hd : DenseRange ((spatialTensorKernelIdeal q α β).quotientStarHom.comp
      (spatialCompletionMap α β)) :=
    (spatialTensorKernelIdeal q α β).quotientMap_surjective.denseRange.comp
      (representedSpatialTensor_dense α β)
      (map_continuous (spatialTensorKernelIdeal q α β).quotientStarHom)
  apply hd.mono
  rintro _ ⟨z, rfl⟩
  exact ⟨algebraicStarTensorMap q (StarAlgHom.id ℂ B) z,
    algebraicQuotientTensorLift_map q hq α β z⟩

variable (γ : C →⋆ₐ[ℂ] (L →L[ℂ] L))
variable (hα : Function.Injective α) (hβ : Function.Injective β)

lemma spatialTensorQuotientFactor_lift (z : C ⊗[ℂ] B) :
    spatialTensorQuotientFactor q α β γ hα hβ (algebraicQuotientTensorLift q hq α β z) =
      spatialCompletionMap γ β z := by
  obtain ⟨w, rfl⟩ := (TensorProduct.map_surjective
    (g := q.toLinearMap) (g' := (StarAlgHom.id ℂ B).toLinearMap) hq Function.surjective_id) z
  rw [← algebraicStarTensorMap_eq, algebraicQuotientTensorLift_map,
    spatialTensorQuotientFactor_map, spatialTensorQuotientMap_tensor]

include hα hβ in
lemma algebraicQuotientTensorLift_injective (hγ : Function.Injective γ) :
    Function.Injective (algebraicQuotientTensorLift q hq α β) := by
  intro x y hxy
  apply spatialStarTensorHom_injective_of_faithful γ β hγ hβ
  have h := congrArg (spatialTensorQuotientFactor q α β γ hα hβ) hxy
  rw [spatialTensorQuotientFactor_lift, spatialTensorQuotientFactor_lift] at h
  exact congrArg Subtype.val h
end CuntzPureness

end

end OAI
