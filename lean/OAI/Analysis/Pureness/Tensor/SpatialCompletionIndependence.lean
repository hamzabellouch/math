import OAI.Analysis.Pureness.Tensor.SpatialRepresentationIndependence
import Mathlib.Analysis.Normed.Operator.Extend

namespace OAI
noncomputable section
namespace CuntzPureness
open CuntzComparison
open scoped TensorProduct InnerProductSpace

section DenseCompletion
variable {R E F : Type*} [Ring R] [StarRing R] [Algebra ℂ R]
variable [CStarAlgebra E] [CStarAlgebra F]
variable (f : R →⋆ₐ[ℂ] E) (g : R →⋆ₐ[ℂ] F)
variable (hf : DenseRange f) (hg : DenseRange g) (hn : ∀ x, ‖g x‖ = ‖f x‖)

def denseStarCompletionLinearEquiv : E ≃ₗᵢ[ℂ] F :=
  (LinearEquiv.refl ℂ R).extendOfIsometry f.toLinearMap g.toLinearMap hf hg hn

lemma denseStarCompletionLinearEquiv_apply (x : R) :
    denseStarCompletionLinearEquiv f g hf hg hn (f x) = g x :=
  LinearEquiv.extendOfIsometry_eq _ _ _ hf hg hn x

def denseStarCompletionEquiv : E ≃⋆ₐ[ℂ] F where
  __ := (denseStarCompletionLinearEquiv f g hf hg hn).toLinearEquiv
  map_mul' := by
    let L := denseStarCompletionLinearEquiv f g hf hg hn
    refine hf.induction_on₂ ?_ ?_
    · exact isClosed_eq (L.continuous.comp continuous_mul)
        ((L.continuous.comp continuous_fst).mul (L.continuous.comp continuous_snd))
    · intro x y
      change L (f x * f y) = L (f x) * L (f y)
      have heq := denseStarCompletionLinearEquiv_apply f g hf hg hn
      rw [← map_mul, heq, heq, heq, map_mul]
  map_star' := by
    intro x
    let L := denseStarCompletionLinearEquiv f g hf hg hn
    refine hf.induction_on x ?_ ?_
    · exact isClosed_eq (L.continuous.comp continuous_star) L.continuous.star
    · intro y
      change L (star (f y)) = star (L (f y))
      have heq := denseStarCompletionLinearEquiv_apply f g hf hg hn
      rw [← map_star, heq, heq, map_star]

lemma denseStarCompletionEquiv_apply (x : R) :
    denseStarCompletionEquiv f g hf hg hn (f x) = g x :=
  denseStarCompletionLinearEquiv_apply f g hf hg hn x

lemma denseStarCompletionEquiv_norm (x : E) :
    ‖denseStarCompletionEquiv f g hf hg hn x‖ = ‖x‖ :=
  (denseStarCompletionLinearEquiv f g hf hg hn).norm_map x
end DenseCompletion

variable {A B H K H' K' : Type*}
variable [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
variable [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [CompleteSpace H']
variable [NormedAddCommGroup K'] [InnerProductSpace ℂ K'] [CompleteSpace K']
variable (α : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (β : B →⋆ₐ[ℂ] (K →L[ℂ] K))
variable (α' : A →⋆ₐ[ℂ] (H' →L[ℂ] H')) (β' : B →⋆ₐ[ℂ] (K' →L[ℂ] K'))
variable (hα : Function.Injective α) (hβ : Function.Injective β)
variable (hα' : Function.Injective α') (hβ' : Function.Injective β')

def representedSpatialEquiv : representedSpatialTensor α β ≃⋆ₐ[ℂ] representedSpatialTensor α' β' :=
  denseStarCompletionEquiv
    (commutingTensorClosureMap _ _ _) (commutingTensorClosureMap _ _ _)
    (representedSpatialTensor_dense α β) (representedSpatialTensor_dense α' β')
    (fun z => (spatialStarTensor_norm_representation_independent α β α' β' hα hβ hα' hβ' z).symm)

lemma representedSpatialEquiv_tensor (z : A ⊗[ℂ] B) :
    representedSpatialEquiv α β α' β' hα hβ hα' hβ'
      (commutingTensorClosureMap _ _ _ z) = commutingTensorClosureMap _ _ _ z :=
  denseStarCompletionEquiv_apply _ _ _ _ _ z

lemma representedSpatialEquiv_norm (x : representedSpatialTensor α β) :
    ‖representedSpatialEquiv α β α' β' hα hβ hα' hβ' x‖ = ‖x‖ :=
  denseStarCompletionEquiv_norm _ _ _ _ _ x
end CuntzPureness

end

end OAI
