import OAI.Analysis.KadisonKastler.TwoStateModularIdentification
import OAI.Analysis.KadisonKastler.TwoStateCocycleContinuity
import OAI.Analysis.KadisonKastler.CocycleCoreTransport

namespace OAI

/-! # A constructed cocycle comparing two faithful cyclic vector states

The two-by-two matrix modular action yields a strongly-star continuous
unitary cocycle. Its diagonal restrictions are identified through the actual
closed Tomita graphs. Thus the cores of the two constructed modular groups
are isomorphic without a change-of-state premise.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H]
  (M : VonNeumannAlgebra H) (Ω ξ : H)
  (hΩc : DenseRange (algebraVectorMap M Ω)) (hξc : DenseRange (algebraVectorMap M ξ))
  (hΩs : Function.Injective (algebraVectorMap M Ω))
  (hξs : Function.Injective (algebraVectorMap M ξ))
  (J K : H ≃ₗᵢ⋆[ℂ] H)
  (L : TwoStateMatrixHilbert H H ≃ₗᵢ⋆[ℂ] TwoStateMatrixHilbert H H)

def constructedStateCocycle : ModularActionCocycle M
    (twoStateCornerResolution M Ω ξ hΩc hξc hΩs hξs J 0).group
    (twoStateCornerResolution M Ω ξ hΩc hξc hΩs hξs K 1).group where
  value t := Unitary.map (StarMonoidHom.ofClass M.toStarSubalgebra.subtype)
    (twoStateCornerCocycle M Ω ξ (twoStateConstructedResolution M Ω ξ hΩc hξc hΩs hξs L) t)
  mem t := (twoStateCornerCocycle M Ω ξ
    (twoStateConstructedResolution M Ω ξ hΩc hξc hΩs hξs L) t : Algebra M).property
  continuous x := twoStateCornerCocycle_continuous M Ω ξ _ x
  continuous_star x := twoStateCornerCocycle_star_continuous M Ω ξ _ x
  value_mul s t := by
    have h := congrArg Subtype.val (twoStateCornerCocycle_mul M Ω ξ
      (twoStateConstructedResolution M Ω ξ hΩc hξc hΩs hξs L) s t)
    rw [twoStateCornerAction_identification M Ω ξ hΩc hξc hΩs hξs J L] at h
    exact h
  action t a ha := by
    have h := congrArg Subtype.val (twoStateCornerAction_conjugate M Ω ξ
      (twoStateConstructedResolution M Ω ξ hΩc hξc hΩs hξs L) t ⟨a, ha⟩)
    rw [twoStateCornerAction_identification M Ω ξ hΩc hξc hΩs hξs K L,
      twoStateCornerAction_identification M Ω ξ hΩc hξc hΩs hξs J L] at h
    exact h

include L in
theorem constructed_state_core_equiv :
    Nonempty (Algebra (regularCoreAlgebra
      (twoStateCornerResolution M Ω ξ hΩc hξc hΩs hξs J 0).group
      (twoStateCornerResolution M Ω ξ hΩc hξc hΩs hξs J 0).continuous M) ≃⋆ₐ[ℂ]
      Algebra (regularCoreAlgebra
        (twoStateCornerResolution M Ω ξ hΩc hξc hΩs hξs K 1).group
        (twoStateCornerResolution M Ω ξ hΩc hξc hΩs hξs K 1).continuous M)) :=
  (constructedStateCocycle M Ω ξ hΩc hξc hΩs hξs J K L).core_equiv
    (twoStateCornerResolution M Ω ξ hΩc hξc hΩs hξs J 0).continuous
    (twoStateCornerResolution M Ω ξ hΩc hξc hΩs hξs K 1).continuous

end

end KadisonKastler

end OAI
