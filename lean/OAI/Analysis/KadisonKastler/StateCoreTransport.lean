import OAI.Analysis.KadisonKastler.StateModularTransport
import OAI.Analysis.KadisonKastler.RegularCoreSpatialTransport

namespace OAI

/-! # Cores of state-preserving cyclic representations

The modular groups give spatially isomorphic concrete cores.
-/

namespace KadisonKastler

noncomputable section

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  {M : VonNeumannAlgebra H} {N : VonNeumannAlgebra K}
  (θ : Algebra M ≃⋆ₐ[ℂ] Algebra N) (Ω : H) (ξ : K)
  (hM : DenseRange (algebraVectorMap M Ω))
  (hN : DenseRange (algebraVectorMap N ξ))
  (hstate : ∀ a : Algebra M, inner ℂ Ω (a.val Ω) = inner ℂ ξ ((θ a).val ξ))

theorem statePreservingUnitary_algebra :
    spatialTransportAlgebra (statePreservingUnitary θ Ω ξ hM hN hstate) M = N := by
  apply SetLike.coe_injective
  ext a
  change a ∈ (statePreservingUnitary θ Ω ξ hM hN hstate).conjStarAlgEquiv ''
    (M : Set (H →L[ℂ] H)) ↔ a ∈ N
  constructor
  · rintro ⟨b, hb, rfl⟩
    rw [statePreservingUnitary_conjugates θ Ω ξ hM hN hstate ⟨b, hb⟩]
    exact (θ ⟨b, hb⟩).property
  · intro ha
    obtain ⟨b, hb⟩ := θ.surjective ⟨a, ha⟩
    refine ⟨b.val, b.property, ?_⟩
    rw [statePreservingUnitary_conjugates θ Ω ξ hM hN hstate b]
    exact congrArg Subtype.val hb

variable [TopologicalSpace.SeparableSpace H] [TopologicalSpace.SeparableSpace K]
  (J : H ≃ₗᵢ⋆[ℂ] H) (L : K ≃ₗᵢ⋆[ℂ] K)
  (hMsep : Function.Injective (algebraVectorMap M Ω))
  (hNsep : Function.Injective (algebraVectorMap N ξ))

include θ hstate in
theorem constructedCore_equiv_of_statePreserving :
    Nonempty (Algebra (regularCoreAlgebra (modularStrongGroup J Ω hMsep hM)
      (modularStrongGroup_continuous J Ω hMsep hM) M) ≃⋆ₐ[ℂ]
      Algebra (regularCoreAlgebra (modularStrongGroup L ξ hNsep hN)
        (modularStrongGroup_continuous L ξ hNsep hN) N)) :=
  regularCore_equiv_of_spatial (statePreservingUnitary θ Ω ξ hM hN hstate)
    (modularStrongGroup J Ω hMsep hM) (modularStrongGroup L ξ hNsep hN)
    (modularStrongGroup_continuous J Ω hMsep hM)
    (modularStrongGroup_continuous L ξ hNsep hN)
    (statePreservingUnitary_modular θ Ω ξ hM hN hstate J L hMsep hNsep)
    M N (statePreservingUnitary_algebra θ Ω ξ hM hN hstate)

end

end KadisonKastler

end OAI
