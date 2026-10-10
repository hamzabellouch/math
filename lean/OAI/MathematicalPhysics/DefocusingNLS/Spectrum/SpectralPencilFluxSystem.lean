import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralFluxSmoothness

namespace OAI

/-! The exact limiting compact-pencil kernel supplies the classical exterior flux system. -/

open Set
open scoped ContDiff
namespace DefocusingNLS.SpectralPenaltyFamily
variable {R l : ℝ}

theorem limitPencil_flux_system (s : SpectralPenaltyFamily R l) (ell : ℕ)
    (hl : 0 < l) (hlR : l < R) (a : SpectralHarmonicWeight R) (c ζ : ℂ)
    (B : ℂ × ℂ →L[ℂ] ℂ × ℂ)
    (hw : ContinuousOn s.limitWeight.density (Ioo 0 R))
    (ha : ContinuousOn a.density (Ioo 0 R))
    (hpos : ∀ x ∈ Ioo 0 R, 0 < s.limitWeight.density x)
    (z : SpectralRadialObservationSpace R)
    (hz : s.limitPencil ell hl hlR (spectralLowerOrderOperator ell R (hl.trans hlR)
      (spectralRadialWeightMultiplier R s.limitWeight)
      (spectralRadialWeightMultiplier R a) c ζ B) z=z) :
    ∃ u : SpectralHarmonicPair ell R, u ∈ spectralHarmonicCoreSubspace ell R l ∧
      spectralHarmonicObservation ell R (hl.trans hlR) u=z ∧
      (∀ x ∈ Ioo l R, HasDerivAt (spectralFluxState ell R (hl.trans hlR) s.limitWeight a u)
        (spectralFluxField ell (s.limitWeight.density x) (a.density x) c ζ x
          (spectralFluxState ell R (hl.trans hlR) s.limitWeight a u x)) x) ∧
      ∀ α β : ℝ, l < α → β < R →
        ContDiffOn ℝ ∞ s.limitWeight.density (Icc α β) →
        ContDiffOn ℝ ∞ a.density (Icc α β) →
        ContDiffOn ℝ ∞ (spectralFluxState ell R (hl.trans hlR) s.limitWeight a u) (Icc α β) := by
  obtain ⟨u,hu,hobs,hweak⟩ := (s.limitPencil_complex_variational ell hl hlR _ z).mp hz
  have he : ∀ v : spectralHarmonicCoreSubspace ell R l,
      spectralHarmonicPairComplexForm ell R s.limitWeight u v=
      inner ℂ (spectralLowerOrderOperator ell R (hl.trans hlR)
        (spectralRadialWeightMultiplier R s.limitWeight) (spectralRadialWeightMultiplier R a)
        c ζ B (spectralHarmonicObservation ell R (hl.trans hlR) u)) v := by
    simpa only [hobs] using hweak
  exact ⟨u,hu,hobs,fun x hx =>
    spectralFluxState_hasDerivAt ell R l (hl.trans hlR) hl s.limitWeight a u c ζ B hw ha hpos he x hx,
    fun α β hα hβ hμ hA => spectralFluxState_contDiffOn_annulus ell R l α β
      (hl.trans hlR) hl hα hβ s.limitWeight a u c ζ B hw ha hpos hμ hA he⟩

end DefocusingNLS.SpectralPenaltyFamily

end OAI
