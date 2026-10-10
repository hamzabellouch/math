import OAI.Analysis.Pureness.Completion.DenseStarCompletionMap
import OAI.Analysis.Pureness.Tensor.SpatialTensorFunctoriality
import OAI.Analysis.Pureness.Operators.CStarHomClosedRange
import Mathlib.LinearAlgebra.TensorProduct.RightExactness

namespace OAI
noncomputable section
namespace CuntzPureness
open CuntzComparison
open scoped TensorProduct InnerProductSpace CStarAlgebra
variable {A B C D H K H' K' : Type*}
variable [CStarAlgebra A]
variable [CStarAlgebra B]
variable [CStarAlgebra C] [CStarAlgebra D]
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
variable [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [CompleteSpace H']
variable [NormedAddCommGroup K'] [InnerProductSpace ℂ K'] [CompleteSpace K']

def algebraicStarTensorMap (ι : A →⋆ₐ[ℂ] C) (κ : B →⋆ₐ[ℂ] D) :
    A ⊗[ℂ] B →⋆ₐ[ℂ] C ⊗[ℂ] D :=
  { Algebra.TensorProduct.map ι.toAlgHom κ.toAlgHom with
    map_star' := by
      intro z
      induction z using TensorProduct.inductionOn with
      | tmul a b =>
        change ι (star a) ⊗ₜ[ℂ] κ (star b) = star (ι a) ⊗ₜ[ℂ] star (κ b)
        rw [map_star, map_star]
      | add x y hx hy => simpa using congrArg₂ (· + ·) hx hy }

lemma algebraicStarTensorMap_eq (ι : A →⋆ₐ[ℂ] C) (κ : B →⋆ₐ[ℂ] D) (z : A ⊗[ℂ] B) :
    algebraicStarTensorMap ι κ z = TensorProduct.map ι.toLinearMap κ.toLinearMap z := rfl

abbrev spatialCompletionMap
    (α : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (β : B →⋆ₐ[ℂ] (K →L[ℂ] K)) :
    A ⊗[ℂ] B →⋆ₐ[ℂ] representedSpatialTensor α β :=
  by exact commutingTensorClosureMap _ _ _

variable [PartialOrder A] [StarOrderedRing A] [PartialOrder B] [StarOrderedRing B]
variable (α : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (β : B →⋆ₐ[ℂ] (K →L[ℂ] K))
variable (γ : C →⋆ₐ[ℂ] (H' →L[ℂ] H')) (δ : D →⋆ₐ[ℂ] (K' →L[ℂ] K'))
variable (hα : Function.Injective α) (hβ : Function.Injective β)
variable (ι : A →⋆ₐ[ℂ] C) (κ : B →⋆ₐ[ℂ] D)

def completedSpatialTensorMap : representedSpatialTensor α β →⋆ₐ[ℂ]
    representedSpatialTensor γ δ := by
  refine denseStarCompletionHom (E := representedSpatialTensor α β)
    (F := representedSpatialTensor γ δ) (spatialCompletionMap α β)
    ((spatialCompletionMap γ δ).comp (algebraicStarTensorMap ι κ))
    (representedSpatialTensor_dense α β) ?_
  intro z
  change ‖spatialStarTensorHom γ δ (TensorProduct.map ι.toLinearMap κ.toLinearMap z)‖ ≤
    ‖spatialStarTensorHom α β z‖
  exact spatialStarTensor_map_norm_le α β hα hβ ι κ γ δ z

lemma completedSpatialTensorMap_tensor (z : A ⊗[ℂ] B) :
    completedSpatialTensorMap α β γ δ hα hβ ι κ (spatialCompletionMap α β z) =
      spatialCompletionMap γ δ (TensorProduct.map ι.toLinearMap κ.toLinearMap z) :=
  denseStarCompletionHom_apply _ _ _ _ z

lemma completedSpatialTensorMap_norm_le (x : representedSpatialTensor α β) :
    ‖completedSpatialTensorMap α β γ δ hα hβ ι κ x‖ ≤ ‖x‖ :=
  NonUnitalStarAlgHom.norm_apply_le _ _

lemma completedSpatialTensorMap_unique
    (L : representedSpatialTensor α β →⋆ₐ[ℂ] representedSpatialTensor γ δ)
    (hL : ∀ z, L (spatialCompletionMap α β z) =
      spatialCompletionMap γ δ (TensorProduct.map ι.toLinearMap κ.toLinearMap z)) :
    L = completedSpatialTensorMap α β γ δ hα hβ ι κ :=
  denseStarCompletionHom_unique _ _ _ _ L hL

lemma completedSpatialTensorMap_denseRange
    (hι : Function.Surjective ι) (hκ : Function.Surjective κ) :
    DenseRange (completedSpatialTensorMap α β γ δ hα hβ ι κ) := by
  apply denseStarCompletionHom_denseRange
  have hs : Function.Surjective (algebraicStarTensorMap ι κ) :=
    TensorProduct.map_surjective hι hκ
  exact by
    apply (representedSpatialTensor_dense γ δ).mono
    rintro _ ⟨z, rfl⟩
    obtain ⟨w, rfl⟩ := hs z
    exact ⟨w, rfl⟩

lemma completedSpatialTensorMap_surjective
    (hι : Function.Surjective ι) (hκ : Function.Surjective κ) :
    Function.Surjective (completedSpatialTensorMap α β γ δ hα hβ ι κ) := by
  let := CStarAlgebra.spectralOrder (representedSpatialTensor α β)
  let := CStarAlgebra.spectralOrderedRing (representedSpatialTensor α β)
  exact starHom_surjective_of_denseRange _
    (completedSpatialTensorMap_denseRange α β γ δ hα hβ ι κ hι hκ)

lemma completedSpatialTensorMap_isometry
    (hι : Function.Injective ι) (hκ : Function.Injective κ)
    (hγ : Function.Injective γ) (hδ : Function.Injective δ) :
    Isometry (completedSpatialTensorMap α β γ δ hα hβ ι κ) := by
  apply AddMonoidHomClass.isometry_of_norm
  intro x
  refine (representedSpatialTensor_dense α β).induction_on x
    (isClosed_eq (continuous_norm.comp (map_continuous _)) continuous_norm) ?_
  intro z
  rw [completedSpatialTensorMap_tensor]
  exact spatialStarTensor_map_norm_eq α β hα hβ ι κ hι hκ γ δ hγ hδ z
end CuntzPureness

end

end OAI
