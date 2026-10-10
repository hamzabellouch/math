import OAI.Analysis.KadisonKastler.StateSymmetry

namespace OAI

/-! # Commutation of state-preserving groups with the canonical modular group -/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H} (Ω : H)
  (U : Multiplicative ℝ →* unitary (H →L[ℂ] H))
  (hU : ∀ t a, a ∈ M → unitaryConj (U t) a ∈ M)

include hU in
theorem stateGroup_normalizes (t : Multiplicative ℝ) : Conjugates (U t) M M := by
  change unitaryConj (U t) '' (M : Set (H →L[ℂ] H)) = (M : Set (H →L[ℂ] H))
  apply Set.Subset.antisymm
  · rintro _ ⟨a, ha, rfl⟩
    exact hU t a ha
  · intro a ha
    have hi : star (U t) = U t⁻¹ := by
      change (U t)⁻¹ = U t⁻¹
      exact (map_inv U t).symm
    refine ⟨unitaryConj (star (U t)) a, ?_, ?_⟩
    · rw [hi]
      exact hU t⁻¹ a ha
    · simpa only [star_star] using unitaryConj_star_unitaryConj (star (U t)) a

variable (hfix : ∀ t, (U t : H →L[ℂ] H) Ω = Ω)
  (hcyc : DenseRange (algebraVectorMap M Ω))

include hU hfix hcyc in
theorem stateGroup_commutes_resolvent (J : H ≃ₗᵢ⋆[ℂ] H) (s : Multiplicative ℝ) (c : ℝ) :
    Commute (U s : H →L[ℂ] H) (graphResolvent M J Ω c) := by
  apply ContinuousLinearMap.ext
  intro x
  exact stateSymmetry_resolvent Ω (U s) (stateGroup_normalizes U hU s) (hfix s) hcyc J c x

variable [TopologicalSpace.SeparableSpace H]
  (hsep : Function.Injective (algebraVectorMap M Ω))

include hU hfix hcyc in
theorem stateGroup_commutes_modular (J : H ≃ₗᵢ⋆[ℂ] H) (s t : Multiplicative ℝ) :
    Commute (U s : H →L[ℂ] H) (modularStrongGroup J Ω hsep hcyc t : H →L[ℂ] H) := by
  apply ContinuousLinearMap.ext
  intro x
  exact stateSymmetry_modular Ω (U s) (stateGroup_normalizes U hU s) (hfix s) hcyc hsep J t x

end

end KadisonKastler

end OAI
