import OAI.Analysis.Pureness.Tensor.CauchySpatialNullDescent

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

def cauchySpatialFactorEquiv :
    SpatialTensorIdealQuotient (T.cauchyQuotientStarHom ht) α
      (reducedGroupAlgebra (FreeGroup ℕ)).subtype ≃⋆ₐ[ℂ]
        representedSpatialTensor γ (reducedGroupAlgebra (FreeGroup ℕ)).subtype :=
  StarAlgEquiv.ofBijective (spatialTensorQuotientFactor (T.cauchyQuotientStarHom ht) α
    (reducedGroupAlgebra (FreeGroup ℕ)).subtype γ hα Subtype.val_injective)
    ⟨T.cauchyFreeGroupTensorFactor_injective ht α γ hα hγ,
      spatialTensorQuotientFactor_surjective _ _ _ _ _ _ (T.cauchyQuotientMap_surjective ht)⟩

def cauchySpatialExtension :
    representedSpatialTensor γ (reducedGroupAlgebra (FreeGroup ℕ)).subtype →⋆ₐ[ℂ]
      U.CauchyQuotient hu :=
  ((spatialTensorKernelIdeal (T.cauchyQuotientStarHom ht) α
    (reducedGroupAlgebra (FreeGroup ℕ)).subtype).liftStarHom
    (T.cauchySpatialAmbientQuotient U ht hu α δ hα Φ l r hΦ c hl)
    (T.cauchySpatialAmbientQuotient_ideal_zero U ht hu α δ hα Φ l r hΦ c hl)).comp
      (T.cauchySpatialFactorEquiv ht α hα γ hγ).symm.toStarAlgHom

lemma cauchySpatialExtension_map
    (x : representedSpatialTensor α (reducedGroupAlgebra (FreeGroup ℕ)).subtype) :
    T.cauchySpatialExtension U ht hu α δ hα Φ l r hΦ c hl γ hγ
      (T.cauchyFreeGroupTensorMap ht α γ hα x) =
        T.cauchySpatialAmbientQuotient U ht hu α δ hα Φ l r hΦ c hl x := by
  let e := T.cauchySpatialFactorEquiv ht α hα γ hγ
  let J := spatialTensorKernelIdeal (T.cauchyQuotientStarHom ht) α
    (reducedGroupAlgebra (FreeGroup ℕ)).subtype
  change J.liftStarHom
    (T.cauchySpatialAmbientQuotient U ht hu α δ hα Φ l r hΦ c hl)
    (T.cauchySpatialAmbientQuotient_ideal_zero U ht hu α δ hα Φ l r hΦ c hl)
    (e.symm (e (J.quotientStarHom x))) = _
  exact congrArg
    (J.liftStarHom (T.cauchySpatialAmbientQuotient U ht hu α δ hα Φ l r hΦ c hl)
      (T.cauchySpatialAmbientQuotient_ideal_zero U ht hu α δ hα Φ l r hΦ c hl))
    (e.symm_apply_apply (J.quotientStarHom x))

lemma cauchySpatialExtension_tensor (x : T.CauchyQuotient ht) (b : ReducedFreeGroup) :
    T.cauchySpatialExtension U ht hu α δ hα Φ l r hΦ c hl γ hγ
      (spatialCompletionMap γ (reducedGroupAlgebra (FreeGroup ℕ)).subtype (x ⊗ₜ[ℂ] b)) =
        T.proportionalQuotientFunctor U ht hu l.toNonUnitalStarAlgHom c hl x *
          U.quotientEmbedding hu (r b) := by
  refine Quotient.inductionOn x ?_
  intro u
  let z := spatialCompletionMap α (reducedGroupAlgebra (FreeGroup ℕ)).subtype (u ⊗ₜ[ℂ] b)
  let v := T.proportionalCauchyFunctor U ht hu l.toNonUnitalStarAlgHom c hl u
  let w := U.constantCauchy hu (r b)
  have hr : T.cauchySpatialAmbientSequenceHom U ht hu α δ hα Φ l r hΦ c hl z = v*w := by
    apply Subtype.ext
    apply lp.ext
    funext n
    exact T.cauchySpatialAmbientProduct_tensor ht α δ hα Φ l r hΦ u b n
  have hm := congrArg (T.cauchySpatialExtension U ht hu α δ hα Φ l r hΦ c hl γ hγ)
    (T.cauchyFreeGroupTensorMap_tensor ht α γ hα u b)
  have hn := T.cauchySpatialExtension_map U ht hu α δ hα Φ l r hΦ c hl γ hγ z
  exact hm.symm.trans (hn.trans ((congrArg (U.cauchyQuotientStarHom hu) hr).trans
    (_root_.map_mul (U.cauchyQuotientStarHom hu) v w)))

variable (hst : ∀ a b : Positive D, Real.sqrt (T (Positive.add a b)) ≤ Real.sqrt (T a)+Real.sqrt (T b))
variable (hsu : ∀ a b : Positive E, Real.sqrt (U (Positive.add a b)) ≤ Real.sqrt (U a)+Real.sqrt (U b))

lemma cauchySpatialExtension_left_value (x : T.CauchyQuotient ht) :
    U.quotientValue hu hsu (T.cauchySpatialExtension U ht hu α δ hα Φ l r hΦ c hl γ hγ
      (spatialCompletionMap γ (reducedGroupAlgebra (FreeGroup ℕ)).subtype (x ⊗ₜ[ℂ] 1))) =
        (c : ℂ)*T.quotientValue ht hst x := by
  rw [T.cauchySpatialExtension_tensor,_root_.map_one,_root_.map_one,mul_one]
  exact T.proportionalQuotientFunctor_value U ht hu l.toNonUnitalStarAlgHom c hl hst hsu x

lemma cauchySpatialExtension_right_value (b : ReducedFreeGroup) :
    U.quotientValue hu hsu (T.cauchySpatialExtension U ht hu α δ hα Φ l r hΦ c hl γ hγ
      (spatialCompletionMap γ (reducedGroupAlgebra (FreeGroup ℕ)).subtype (1 ⊗ₜ[ℂ] b))) =
        U.complexValue (r b) := by
  rw [T.cauchySpatialExtension_tensor]
  have he : T.proportionalQuotientFunctor U ht hu l.toNonUnitalStarAlgHom c hl 1 = 1 := by
    change U.cauchyQuotientMap hu (T.proportionalCauchyFunctor U ht hu l.toNonUnitalStarAlgHom c hl 1) = 1
    have hh : T.proportionalCauchyFunctor U ht hu l.toNonUnitalStarAlgHom c hl 1 = 1 := by
      apply Subtype.ext
      apply lp.ext
      funext n
      exact l.map_one
    rw [hh,_root_.map_one]
  rw [he,one_mul,U.quotientValue_embedding]
end CuntzPureness.PositiveQuasitrace

end

end OAI
