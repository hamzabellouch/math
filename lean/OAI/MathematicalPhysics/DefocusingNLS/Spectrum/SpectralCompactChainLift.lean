import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralPencilComplexEquation

namespace OAI

/-! A first-order chain for the actual compact pencil lifts to the constrained
weak equations, with both the volume and boundary derivative load retained. -/

namespace DefocusingNLS.SpectralPenaltyFamily
variable {R l : ℝ}

theorem limitInverse_complex_load (s : SpectralPenaltyFamily R l) (ell : ℕ)
    (hl : 0 < l) (hlR : l < R) (F : SpectralHarmonicPair ell R) :
    let u := s.limitInverse ell (InnerProductSpace.toDual ℝ (SpectralHarmonicPair ell R) F)
    u ∈ spectralHarmonicCoreSubspace ell R l ∧
      spectralHarmonicObservation ell R (hl.trans hlR) u = s.observedComplexLimit ell hl hlR F ∧
      ∀ v : SpectralHarmonicCore ell R l,
        spectralHarmonicPairComplexForm ell R s.limitWeight u v = inner ℂ F v := by
  let u := s.limitInverse ell (InnerProductSpace.toDual ℝ (SpectralHarmonicPair ell R) F)
  have hreal (v : SpectralHarmonicCore ell R l) :
      spectralHarmonicPairForm ell R s.limitWeight u v = inner ℝ F v :=
    spectralHarmonicCoreInverse_equation ell R l s.limitWeight s.lower s.lower_pos
      s.limit_radial_lower s.limit_angular_lower _ v
  refine ⟨spectralHarmonicCoreInverse_mem ell R l s.limitWeight s.lower s.lower_pos
    s.limit_radial_lower s.limit_angular_lower _, rfl, ?_⟩
  intro v
  apply spectralHarmonicPairComplexForm_of_real
  · exact hreal v
  · exact hreal ⟨Complex.I • (v : SpectralHarmonicPair ell R),
      spectralHarmonicCore_smul_mem ell R l v v.property Complex.I⟩

theorem limitPencil_chain_lift (s : SpectralPenaltyFamily R l) (ell : ℕ)
    (hl : 0 < l) (hlR : l < R)
    (K D : SpectralRadialObservationSpace R →L[ℂ] SpectralHarmonicPair ell R)
    (z₀ z₁ : SpectralRadialObservationSpace R)
    (h₀ : s.limitPencil ell hl hlR K z₀ = z₀)
    (h₁ : z₁ - s.limitPencil ell hl hlR K z₁ = s.limitPencil ell hl hlR D z₀) :
    ∃ u₀ u₁ : SpectralHarmonicPair ell R,
      u₀ ∈ spectralHarmonicCoreSubspace ell R l ∧
      u₁ ∈ spectralHarmonicCoreSubspace ell R l ∧
      spectralHarmonicObservation ell R (hl.trans hlR) u₀ = z₀ ∧
      spectralHarmonicObservation ell R (hl.trans hlR) u₁ = z₁ ∧
      (∀ v : SpectralHarmonicCore ell R l,
        spectralHarmonicPairComplexForm ell R s.limitWeight u₀ v = inner ℂ (K z₀) v) ∧
      ∀ v : SpectralHarmonicCore ell R l,
        spectralHarmonicPairComplexForm ell R s.limitWeight u₁ v = inner ℂ (K z₁ + D z₀) v := by
  obtain ⟨u₀, hu₀, ho₀, he₀⟩ := (s.limitPencil_complex_variational ell hl hlR K z₀).mp h₀
  let u₁ := s.limitInverse ell
    (InnerProductSpace.toDual ℝ (SpectralHarmonicPair ell R) (K z₁ + D z₀))
  obtain ⟨hu₁, ho₁, he₁⟩ := s.limitInverse_complex_load ell hl hlR (K z₁ + D z₀)
  refine ⟨u₀, u₁, hu₀, hu₁, ho₀, ?_, he₀, he₁⟩
  rw [ho₁, map_add]
  change s.limitPencil ell hl hlR K z₁ + s.limitPencil ell hl hlR D z₀ = z₁
  rw [← h₁]
  abel

end DefocusingNLS.SpectralPenaltyFamily

end OAI
