import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralPencilComplexEquation

namespace OAI

/-! A kernel vector lifted with its observation already substituted in the
weak equation. Keeping this step separate avoids unfolding the coefficient
operator during the physical reconstruction. -/

namespace DefocusingNLS.SpectralPenaltyFamily
variable {R l : ℝ}

theorem limitPencil_kernel_lift (s : SpectralPenaltyFamily R l) (ell : ℕ)
    (hl : 0 < l) (hlR : l < R)
    (K : SpectralRadialObservationSpace R →L[ℂ] SpectralHarmonicPair ell R)
    (z : SpectralRadialObservationSpace R) (hz : s.limitPencil ell hl hlR K z = z) :
    ∃ u : SpectralHarmonicPair ell R, u ∈ spectralHarmonicCoreSubspace ell R l ∧
      spectralHarmonicObservation ell R (hl.trans hlR) u = z ∧
      ∀ v : SpectralHarmonicCore ell R l,
        spectralHarmonicPairComplexForm ell R s.limitWeight u v =
          inner ℂ (K (spectralHarmonicObservation ell R (hl.trans hlR) u)) v := by
  obtain ⟨u,hu,ho,he⟩ := (s.limitPencil_complex_variational ell hl hlR K z).mp hz
  refine ⟨u,hu,ho,?_⟩
  intro v
  rw [ho]
  exact he v

end DefocusingNLS.SpectralPenaltyFamily

end OAI
