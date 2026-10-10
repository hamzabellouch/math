import OAI.Analysis.Pureness.Tensor.SpatialRepresentationIndependence

namespace OAI
noncomputable section
namespace CuntzPureness
open CuntzComparison
open scoped TensorProduct InnerProductSpace
variable {A B C D H K H' K' : Type*}
variable [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
variable [CStarAlgebra C] [CStarAlgebra D]
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
variable [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [CompleteSpace H']
variable [NormedAddCommGroup K'] [InnerProductSpace ℂ K'] [CompleteSpace K']

omit [PartialOrder A] [StarOrderedRing A] [PartialOrder B] [StarOrderedRing B] in
lemma spatialStarTensor_map
    (ι : A →⋆ₐ[ℂ] C) (κ : B →⋆ₐ[ℂ] D)
    (γ : C →⋆ₐ[ℂ] (H' →L[ℂ] H')) (δ : D →⋆ₐ[ℂ] (K' →L[ℂ] K')) (z : A ⊗[ℂ] B) :
    spatialStarTensorHom γ δ (TensorProduct.map ι.toLinearMap κ.toLinearMap z) =
      spatialStarTensorHom (γ.comp ι) (δ.comp κ) z := by
  induction z using TensorProduct.inductionOn with
  | add x y hx hy => simpa using congrArg₂ (· + ·) hx hy
  | tmul a b => simp [spatialStarTensorHom_tmul]

theorem spatialStarTensor_map_norm_le
    (α : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (β : B →⋆ₐ[ℂ] (K →L[ℂ] K))
    (hα : Function.Injective α) (hβ : Function.Injective β)
    (ι : A →⋆ₐ[ℂ] C) (κ : B →⋆ₐ[ℂ] D)
    (γ : C →⋆ₐ[ℂ] (H' →L[ℂ] H')) (δ : D →⋆ₐ[ℂ] (K' →L[ℂ] K')) (z : A ⊗[ℂ] B) :
    ‖spatialStarTensorHom γ δ (TensorProduct.map ι.toLinearMap κ.toLinearMap z)‖ ≤
      ‖spatialStarTensorHom α β z‖ := by
  rw [spatialStarTensor_map]
  exact spatialStarTensor_norm_le_faithful _ _ _ _ hα hβ z

theorem spatialStarTensor_map_norm_eq
    (α : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (β : B →⋆ₐ[ℂ] (K →L[ℂ] K))
    (hα : Function.Injective α) (hβ : Function.Injective β)
    (ι : A →⋆ₐ[ℂ] C) (κ : B →⋆ₐ[ℂ] D) (hι : Function.Injective ι) (hκ : Function.Injective κ)
    (γ : C →⋆ₐ[ℂ] (H' →L[ℂ] H')) (δ : D →⋆ₐ[ℂ] (K' →L[ℂ] K'))
    (hγ : Function.Injective γ) (hδ : Function.Injective δ) (z : A ⊗[ℂ] B) :
    ‖spatialStarTensorHom γ δ (TensorProduct.map ι.toLinearMap κ.toLinearMap z)‖ =
      ‖spatialStarTensorHom α β z‖ := by
  rw [spatialStarTensor_map]
  exact spatialStarTensor_norm_representation_independent (γ.comp ι) (δ.comp κ) α β
    (hγ.comp hι) (hδ.comp hκ) hα hβ z
end CuntzPureness

end

end OAI
