import OAI.Analysis.Pureness.Tensor.CauchySpatialExtension

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

lemma cauchySpatialExtension_original_tensor (a : D) (b : ReducedFreeGroup) :
    T.cauchySpatialExtension U ht hu α δ hα Φ l r hΦ c hl γ hγ
      (spatialCompletionMap γ (reducedGroupAlgebra (FreeGroup ℕ)).subtype
        (T.quotientEmbedding ht a ⊗ₜ[ℂ] b)) =
      U.quotientEmbedding hu (Φ (spatialCompletionMap δ
        (reducedGroupAlgebra (FreeGroup ℕ)).subtype (a ⊗ₜ[ℂ] b))) := by
  have h := T.cauchySpatialExtension_tensor U ht hu α δ hα Φ l r hΦ c hl γ hγ
    (T.quotientEmbedding ht a) b
  have hlft := T.proportionalQuotientFunctor_embedding U ht hu l.toNonUnitalStarAlgHom c hl a
  exact h.trans ((congrArg (fun z => z*U.quotientEmbedding hu (r b)) hlft).trans
    ((_root_.map_mul (U.quotientEmbedding hu) (l a) (r b)).symm.trans
      (congrArg (U.quotientEmbedding hu) (hΦ a b).symm)))

lemma cauchySpatialExtension_left_injective (hc : 0 < c) :
    Function.Injective (fun x : T.CauchyQuotient ht =>
      T.cauchySpatialExtension U ht hu α δ hα Φ l r hΦ c hl γ hγ
        (spatialCompletionMap γ (reducedGroupAlgebra (FreeGroup ℕ)).subtype (x ⊗ₜ[ℂ] 1))) := by
  have he (x : T.CauchyQuotient ht) :
      T.cauchySpatialExtension U ht hu α δ hα Φ l r hΦ c hl γ hγ
        (spatialCompletionMap γ (reducedGroupAlgebra (FreeGroup ℕ)).subtype (x ⊗ₜ[ℂ] 1)) =
        T.proportionalQuotientFunctor U ht hu l.toNonUnitalStarAlgHom c hl x := by
    have h := T.cauchySpatialExtension_tensor U ht hu α δ hα Φ l r hΦ c hl γ hγ x 1
    have hr : U.quotientEmbedding hu (r 1) = 1 :=
      (congrArg (U.quotientEmbedding hu) r.map_one).trans (U.quotientEmbedding hu).map_one
    exact h.trans ((congrArg (fun z =>
      T.proportionalQuotientFunctor U ht hu l.toNonUnitalStarAlgHom c hl x*z) hr).trans (mul_one _))
  intro x y hxy
  apply T.proportionalQuotientFunctor_injective U ht hu l.toNonUnitalStarAlgHom c hl hc
  exact (he x).symm.trans (hxy.trans (he y))
end CuntzPureness.PositiveQuasitrace

end

end OAI
