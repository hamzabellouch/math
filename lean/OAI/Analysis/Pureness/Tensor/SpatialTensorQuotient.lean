import OAI.Analysis.Pureness.Tensor.AlgebraicTensorKernel

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
variable (q : A →⋆ₐ[ℂ] C)
variable (α : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (β : B →⋆ₐ[ℂ] (K →L[ℂ] K))
variable (γ : C →⋆ₐ[ℂ] (L →L[ℂ] L))
variable (hα : Function.Injective α) (hβ : Function.Injective β)

abbrev spatialTensorQuotientMap : representedSpatialTensor α β →⋆ₐ[ℂ]
    representedSpatialTensor γ β :=
  completedSpatialTensorMap α β γ β hα hβ q (StarAlgHom.id ℂ B)

lemma spatialTensorQuotientMap_tensor (z : A ⊗[ℂ] B) :
    spatialTensorQuotientMap q α β γ hα hβ (spatialCompletionMap α β z) =
      spatialCompletionMap γ β (algebraicStarTensorMap q (StarAlgHom.id ℂ B) z) :=
  completedSpatialTensorMap_tensor α β γ β hα hβ q (StarAlgHom.id ℂ B) z

lemma spatialTensorQuotientMap_surjective (hq : Function.Surjective q) :
    Function.Surjective (spatialTensorQuotientMap q α β γ hα hβ) :=
  completedSpatialTensorMap_surjective α β γ β hα hβ q (StarAlgHom.id ℂ B) hq
    Function.surjective_id

lemma spatialTensorQuotientMap_ideal_zero (x : representedSpatialTensor α β)
    (hx : x ∈ (spatialTensorKernelIdeal q α β).ideal) :
    spatialTensorQuotientMap q α β γ hα hβ x = 0 :=
  denseKernelClosedIdeal_map_zero _ _ _ _ (spatialCompletionMap γ β)
    (spatialTensorQuotientMap_tensor q α β γ hα hβ) x hx

abbrev SpatialTensorIdealQuotient := (spatialTensorKernelIdeal q α β).Quotient

instance spatialTensorIdealQuotientCStar : CStarAlgebra (SpatialTensorIdealQuotient q α β) := by
  letI := CStarAlgebra.spectralOrder (representedSpatialTensor α β)
  letI := CStarAlgebra.spectralOrderedRing (representedSpatialTensor α β)
  exact ClosedStarIdeal.quotientCStarAlgebra _

def spatialTensorQuotientFactor : SpatialTensorIdealQuotient q α β →⋆ₐ[ℂ]
    representedSpatialTensor γ β :=
  (spatialTensorKernelIdeal q α β).liftStarHom
    (spatialTensorQuotientMap q α β γ hα hβ)
    (spatialTensorQuotientMap_ideal_zero q α β γ hα hβ)

lemma spatialTensorQuotientFactor_map (x : representedSpatialTensor α β) :
    spatialTensorQuotientFactor q α β γ hα hβ
      ((spatialTensorKernelIdeal q α β).quotientStarHom x) =
        spatialTensorQuotientMap q α β γ hα hβ x := rfl

lemma spatialTensorQuotientFactor_surjective (hq : Function.Surjective q) :
    Function.Surjective (spatialTensorQuotientFactor q α β γ hα hβ) := by
  intro x
  obtain ⟨u, rfl⟩ := spatialTensorQuotientMap_surjective q α β γ hα hβ hq x
  exact ⟨(spatialTensorKernelIdeal q α β).quotientStarHom u, rfl⟩

lemma spatialTensorQuotientFactor_norm_le (x : SpatialTensorIdealQuotient q α β) :
    ‖spatialTensorQuotientFactor q α β γ hα hβ x‖ ≤ ‖x‖ :=
  NonUnitalStarAlgHom.norm_apply_le _ _

theorem spatialTensorQuotientFactor_injective_iff :
    Function.Injective (spatialTensorQuotientFactor q α β γ hα hβ) ↔
      ∀ x : representedSpatialTensor α β,
        spatialTensorQuotientMap q α β γ hα hβ x = 0 →
          x ∈ (spatialTensorKernelIdeal q α β).ideal := by
  constructor
  · intro hi x hx
    have he : (spatialTensorKernelIdeal q α β).quotientStarHom x = 0 :=
      hi (hx.trans (map_zero _).symm)
    change (spatialTensorKernelIdeal q α β).ideal.ringCon x 0
    exact Quotient.exact he
  · exact (spatialTensorKernelIdeal q α β).liftStarHom_injective _ _
end CuntzPureness

end

end OAI
