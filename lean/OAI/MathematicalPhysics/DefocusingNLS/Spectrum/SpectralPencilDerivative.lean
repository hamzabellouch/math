import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralPencilLimit
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralCompactChainLift

namespace OAI

/-! Differentiating the compact pencil preserves exactly the derivative
load used in the weak first-chain lift. -/

namespace DefocusingNLS.SpectralPenaltyFamily
variable {R l : ℝ}

noncomputable local instance derivativeCoefficientSpaceNormed (ell : ℕ) (R : ℝ) :
    NormedAddCommGroup (SpectralRadialObservationSpace R →L[ℂ] SpectralHarmonicPair ell R) := by
  let : NormedAddCommGroup (SpectralHarmonicPair ell R) := inferInstance
  let : NormedSpace ℂ (SpectralHarmonicPair ell R) := inferInstance
  let : NormedAddCommGroup (SpectralRadialObservationSpace R) := inferInstance
  let : NormedSpace ℂ (SpectralRadialObservationSpace R) := inferInstance
  exact ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance derivativePencilSpaceNormed (R : ℝ) :
    NormedAddCommGroup (SpectralRadialObservationSpace R →L[ℂ] SpectralRadialObservationSpace R) := by
  let : NormedAddCommGroup (SpectralRadialObservationSpace R) := inferInstance
  let : NormedSpace ℂ (SpectralRadialObservationSpace R) := inferInstance
  exact ContinuousLinearMap.toNormedAddCommGroup

theorem limitPencil_hasDerivAt (s : SpectralPenaltyFamily R l) (ell : ℕ)
    (hl : 0 < l) (hlR : l < R)
    (K : ℂ → SpectralRadialObservationSpace R →L[ℂ] SpectralHarmonicPair ell R)
    (D : SpectralRadialObservationSpace R →L[ℂ] SpectralHarmonicPair ell R)
    (ζ : ℂ) (hK : HasDerivAt K D ζ) :
    HasDerivAt (fun z => s.limitPencil ell hl hlR (K z))
      (s.limitPencil ell hl hlR D) ζ := by
  let L := ContinuousLinearMap.compL ℂ (SpectralRadialObservationSpace R)
    (SpectralHarmonicPair ell R) (SpectralRadialObservationSpace R)
      (s.observedComplexLimit ell hl hlR)
  exact L.hasFDerivAt.comp_hasDerivAt ζ hK

theorem limitPencil_derivative_chain_lift (s : SpectralPenaltyFamily R l) (ell : ℕ)
    (hl : 0 < l) (hlR : l < R)
    (K : ℂ → SpectralRadialObservationSpace R →L[ℂ] SpectralHarmonicPair ell R)
    (D : SpectralRadialObservationSpace R →L[ℂ] SpectralHarmonicPair ell R)
    (ζ : ℂ) (hK : HasDerivAt K D ζ)
    (z₀ z₁ : SpectralRadialObservationSpace R)
    (h₀ : s.limitPencil ell hl hlR (K ζ) z₀ = z₀)
    (h₁ : z₁ - s.limitPencil ell hl hlR (K ζ) z₁ =
      deriv (fun z => s.limitPencil ell hl hlR (K z)) ζ z₀) :
    ∃ u₀ u₁ : SpectralHarmonicPair ell R,
      u₀ ∈ spectralHarmonicCoreSubspace ell R l ∧
      u₁ ∈ spectralHarmonicCoreSubspace ell R l ∧
      spectralHarmonicObservation ell R (hl.trans hlR) u₀ = z₀ ∧
      spectralHarmonicObservation ell R (hl.trans hlR) u₁ = z₁ ∧
      (∀ v : SpectralHarmonicCore ell R l,
        spectralHarmonicPairComplexForm ell R s.limitWeight u₀ v = inner ℂ (K ζ z₀) v) ∧
      ∀ v : SpectralHarmonicCore ell R l,
        spectralHarmonicPairComplexForm ell R s.limitWeight u₁ v = inner ℂ (K ζ z₁ + D z₀) v := by
  rw [(s.limitPencil_hasDerivAt ell hl hlR K D ζ hK).deriv] at h₁
  exact s.limitPencil_chain_lift ell hl hlR (K ζ) D z₀ z₁ h₀ h₁

end DefocusingNLS.SpectralPenaltyFamily

end OAI
