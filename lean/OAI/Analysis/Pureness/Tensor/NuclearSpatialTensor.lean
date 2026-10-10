import OAI.Analysis.Pureness.Tensor.NuclearTensorNorm
import OAI.Analysis.Pureness.Tensor.SpatialCompletionIndependence

namespace OAI
noncomputable section
namespace CuntzPureness
open CuntzComparison
open scoped TensorProduct
universe u v
variable {A : Type u} [CStarAlgebra A] {B : Type v} [CStarAlgebra B]

def IsNuclear.tensorCompletionEquiv (hA : IsNuclear.{u, v} A)
    {E F : Type*} [CStarAlgebra E] [CStarAlgebra F]
    (f : A ⊗[ℂ] B →⋆ₐ[ℂ] E) (g : A ⊗[ℂ] B →⋆ₐ[ℂ] F)
    (hf : Function.Injective f) (hg : Function.Injective g)
    (hfd : DenseRange f) (hgd : DenseRange g) : E ≃⋆ₐ[ℂ] F :=
  denseStarCompletionEquiv f g hfd hgd (fun z =>
    (hA.faithful_tensor_norm_eq f g hf hg z).symm)

lemma IsNuclear.tensorCompletionEquiv_tensor (hA : IsNuclear.{u, v} A)
    {E F : Type*} [CStarAlgebra E] [CStarAlgebra F]
    (f : A ⊗[ℂ] B →⋆ₐ[ℂ] E) (g : A ⊗[ℂ] B →⋆ₐ[ℂ] F)
    (hf : Function.Injective f) (hg : Function.Injective g)
    (hfd : DenseRange f) (hgd : DenseRange g) (z : A ⊗[ℂ] B) :
    hA.tensorCompletionEquiv f g hf hg hfd hgd (f z) = g z :=
  denseStarCompletionEquiv_apply _ _ _ _ _ z

lemma IsNuclear.tensorCompletionEquiv_norm (hA : IsNuclear.{u, v} A)
    {E F : Type*} [CStarAlgebra E] [CStarAlgebra F]
    (f : A ⊗[ℂ] B →⋆ₐ[ℂ] E) (g : A ⊗[ℂ] B →⋆ₐ[ℂ] F)
    (hf : Function.Injective f) (hg : Function.Injective g)
    (hfd : DenseRange f) (hgd : DenseRange g) (x : E) :
    ‖hA.tensorCompletionEquiv f g hf hg hfd hgd x‖ = ‖x‖ :=
  denseStarCompletionEquiv_norm _ _ _ _ _ x

variable [Nontrivial A] (hsimple : TopologicallySimple A)
variable {H K N : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [Nontrivial H]
variable [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
variable [CStarAlgebra N]

include hsimple in

theorem nuclear_spatial_norm_eq_commuting (hA : IsNuclear.{u, v} A)
    (α : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (β : B →⋆ₐ[ℂ] (K →L[ℂ] K))
    (hβ : Function.Injective β) (φ : A →⋆ₐ[ℂ] N) (ψ : B →⋆ₐ[ℂ] N)
    (hψ : Function.Injective ψ) (hc : ∀ a b, Commute (φ a) (ψ b)) (z : A ⊗[ℂ] B) :
    ‖spatialStarTensorHom α β z‖ = ‖commutingStarTensorHom φ ψ hc z‖ :=
  hA.faithful_tensor_norm_eq _ _ (spatialStarTensorHom_injective α β hsimple hβ)
    (commutingStarTensorHom_injective hsimple φ ψ hψ hc) z
end CuntzPureness

end

end OAI
