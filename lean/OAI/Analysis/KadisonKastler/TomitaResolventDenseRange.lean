import OAI.Analysis.KadisonKastler.TomitaPolarCoordinates

namespace OAI

/-! # The dense range used for logarithmic approximation

The product `R(1-R)` of the graph resolvent and its complement has dense range.
This is the precise dense set on which the weighted scalar estimates apply.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] {M : VonNeumannAlgebra H}

private theorem selfAdjoint_denseRange (A : H →L[ℂ] H) (hA : IsSelfAdjoint A)
    (hinj : Function.Injective A) : DenseRange A := by
  change Dense (A.range : Set H)
  rw [Submodule.dense_iff_topologicalClosure_eq_top]
  apply Submodule.orthogonal_eq_bot_iff.mp
  rw [Submodule.orthogonal_closure, A.orthogonal_range]
  have hs : A.adjoint = A := hA.star_eq
  rw [hs]
  exact LinearMap.ker_eq_bot.mpr hinj

theorem graphResolvent_injective (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)
    (hsep : Function.Injective (algebraVectorMap M Ω))
    (hcyc : DenseRange (algebraVectorMap M Ω)) :
    Function.Injective (graphResolvent M J Ω 1) := by
  intro x y he
  apply sub_eq_zero.mp
  apply (graphResolvent_eq_zero_iff J Ω 1 hsep hcyc (x - y)).mp
  rw [map_sub, he, sub_self]

theorem one_sub_graphResolvent_injective (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)
    (hsep : Function.Injective (algebraVectorMap M Ω)) :
    Function.Injective ((1 : H →L[ℂ] H) - graphResolvent M J Ω 1) := by
  intro x y he
  apply sub_eq_zero.mp
  apply (one_sub_graphResolvent_eq_zero_iff J Ω hsep (x - y)).mp
  rw [map_sub, he, sub_self]

/-- This product kills both singular endpoints and still has dense range. -/
def graphResolventCutoff (M : VonNeumannAlgebra H) (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H) : H →L[ℂ] H :=
  graphResolvent M J Ω 1 * (1 - graphResolvent M J Ω 1)

theorem graphResolventCutoff_selfAdjoint (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H) :
    IsSelfAdjoint (graphResolventCutoff M J Ω) := by
  have hr := (graphResolvent_positive (M := M) J Ω 1).isSelfAdjoint
  change star (graphResolvent M J Ω 1 * (1 - graphResolvent M J Ω 1)) =
    graphResolvent M J Ω 1 * (1 - graphResolvent M J Ω 1)
  rw [star_mul, star_sub, star_one, hr.star_eq]
  noncomm_ring

theorem graphResolventCutoff_dense (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)
    (hsep : Function.Injective (algebraVectorMap M Ω))
    (hcyc : DenseRange (algebraVectorMap M Ω)) :
    DenseRange (graphResolventCutoff M J Ω) := by
  apply selfAdjoint_denseRange _ (graphResolventCutoff_selfAdjoint J Ω)
  exact (graphResolvent_injective J Ω hsep hcyc).comp
    (one_sub_graphResolvent_injective J Ω hsep)

end

end KadisonKastler

end OAI
