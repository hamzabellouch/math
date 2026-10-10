import OAI.Analysis.Pureness.Tensor.CauchySpatialOriginalAgreement
import OAI.Analysis.Pureness.Tensor.SpatialFreeGroupFaithful

namespace OAI
noncomputable section
namespace CuntzPureness.PositiveQuasitrace
open CuntzTrace Filter
open scoped TensorProduct Topology ENNReal NNReal
variable {D E H L : Type*}
variable [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D] [Nontrivial D]
variable [CStarAlgebra E] [PartialOrder E] [StarOrderedRing E] [Nontrivial E]
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable [NormedAddCommGroup L] [InnerProductSpace ℂ L] [CompleteSpace L]
variable (T : CuntzPureness.PositiveQuasitrace D) (U : CuntzPureness.PositiveQuasitrace E)
variable (ht : ∀ x y, T.metricSize (x+y) ≤ T.metricSize x+T.metricSize y)
variable (hu : ∀ x y, U.metricSize (x+y) ≤ U.metricSize x+U.metricSize y)
variable (α : T.cauchySequenceAlgebra ht →⋆ₐ[ℂ] (H →L[ℂ] H))
variable (δ : D →⋆ₐ[ℂ] (L →L[ℂ] L)) (hα : Function.Injective α)
variable (Φ : representedSpatialTensor δ (reducedGroupAlgebra (FreeGroup ℕ)).subtype →⋆ₐ[ℂ] E)
variable (l : D →⋆ₐ[ℂ] E) (r : ReducedFreeGroup →⋆ₐ[ℂ] E)
variable (hΦ : ∀ a b, Φ (spatialCompletionMap δ
  (reducedGroupAlgebra (FreeGroup ℕ)).subtype (a ⊗ₜ[ℂ] b)) = l a*r b)
variable (c : ℝ≥0) (hl : ∀ a, U (Positive.map l.toNonUnitalStarAlgHom a) = (c : ℝ)*T a)

variable {K : Type*}
variable [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
variable (γ : T.CauchyQuotient ht →⋆ₐ[ℂ] (K →L[ℂ] K)) (hγ : Function.Injective γ)

lemma cauchySpatialExtension_injective (hc : 0 < c) :
    Function.Injective (T.cauchySpatialExtension U ht hu α δ hα Φ l r hΦ c hl γ hγ) :=
  spatialFreeGroupHom_injective γ hγ _
    (T.cauchySpatialExtension_left_injective U ht hu α δ hα Φ l r hΦ c hl γ hγ hc)
end CuntzPureness.PositiveQuasitrace

end

end OAI
