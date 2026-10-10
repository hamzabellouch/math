import OAI.Analysis.KadisonKastler.ConstructedStateCocycle

namespace OAI

/-! # State independence of the concretely constructed modular core -/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H]
  (M : VonNeumannAlgebra H) (Ω ξ : H)
  (hΩc : DenseRange (algebraVectorMap M Ω)) (hξc : DenseRange (algebraVectorMap M ξ))
  (hΩs : Function.Injective (algebraVectorMap M Ω))
  (hξs : Function.Injective (algebraVectorMap M ξ))
  (J K : H ≃ₗᵢ⋆[ℂ] H)

theorem constructedCore_equiv_of_two_states :
    Nonempty (Algebra (regularCoreAlgebra (modularStrongGroup J Ω hΩs hΩc)
      (modularStrongGroup_continuous J Ω hΩs hΩc) M) ≃⋆ₐ[ℂ]
      Algebra (regularCoreAlgebra (modularStrongGroup K ξ hξs hξc)
        (modularStrongGroup_continuous K ξ hξs hξc) M)) := by
  obtain ⟨L, _⟩ := exists_hilbert_conjugation (H := TwoStateMatrixHilbert H H)
  have h := constructed_state_core_equiv M Ω ξ hΩc hξc hΩs hξs J K L
  exact h

end

end KadisonKastler

end OAI
