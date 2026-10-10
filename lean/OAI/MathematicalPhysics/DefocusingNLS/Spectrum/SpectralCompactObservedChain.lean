import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralCompactChainLift

namespace OAI

/-! Record the lifted chain using its own observations in the weak loads. -/

namespace DefocusingNLS.SpectralPenaltyFamily
variable {R l : ℝ}

theorem limitPencil_observed_chain_lift (s : SpectralPenaltyFamily R l) (ell : ℕ)
    (hl : 0 < l) (hlR : l < R)
    (K D : SpectralRadialObservationSpace R →L[ℂ] SpectralHarmonicPair ell R)
    (z₀ z₁ : SpectralRadialObservationSpace R)
    (h₀ : s.limitPencil ell hl hlR K z₀ = z₀)
    (h₁ : z₁-s.limitPencil ell hl hlR K z₁ = s.limitPencil ell hl hlR D z₀) :
    ∃ u₀ u₁ : SpectralHarmonicPair ell R,
      u₀ ∈ spectralHarmonicCoreSubspace ell R l ∧
      u₁ ∈ spectralHarmonicCoreSubspace ell R l ∧
      spectralHarmonicObservation ell R (hl.trans hlR) u₀=z₀ ∧
      spectralHarmonicObservation ell R (hl.trans hlR) u₁=z₁ ∧
      (∀ v : SpectralHarmonicCore ell R l,
        spectralHarmonicPairComplexForm ell R s.limitWeight u₀ v =
          inner ℂ (K (spectralHarmonicObservation ell R (hl.trans hlR) u₀)) v) ∧
      ∀ v : SpectralHarmonicCore ell R l,
        spectralHarmonicPairComplexForm ell R s.limitWeight u₁ v =
          inner ℂ (K (spectralHarmonicObservation ell R (hl.trans hlR) u₁)+
            D (spectralHarmonicObservation ell R (hl.trans hlR) u₀)) v := by
  obtain ⟨u₀,u₁,hu₀,hu₁,ho₀,ho₁,he₀,he₁⟩ :=
    s.limitPencil_chain_lift ell hl hlR K D z₀ z₁ h₀ h₁
  refine ⟨u₀,u₁,hu₀,hu₁,ho₀,ho₁,?_,?_⟩
  · simpa only [ho₀] using he₀
  · simpa only [ho₀,ho₁] using he₁

end DefocusingNLS.SpectralPenaltyFamily

end OAI
