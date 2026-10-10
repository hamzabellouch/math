import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralWeakRobin
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralPencilComplexEquation

namespace OAI

/-! Every limiting-pencil kernel vector satisfies the actual weighted Robin boundary condition. -/

open Set
namespace DefocusingNLS.SpectralPenaltyFamily
variable {R l : ℝ}

theorem limitPencil_robin (s : SpectralPenaltyFamily R l) (ell : ℕ)
    (hl : 0 < l) (hlR : l < R) (δ : ℝ) (hlδ : l < δ) (hδR : δ < R)
    (a : SpectralHarmonicWeight R) (c ζ : ℂ) (M : ℂ × ℂ →L[ℂ] ℂ × ℂ)
    (hw : ContinuousOn s.limitWeight.density (Ioo 0 R))
    (ha : ContinuousOn a.density (Ioo 0 R))
    (hwc : ContinuousOn s.limitWeight.density (Icc δ R))
    (hac : ContinuousOn a.density (Icc δ R))
    (hpos : ∀ x ∈ Ioo 0 R, 0 < s.limitWeight.density x)
    (hposc : ∀ x ∈ Icc δ R, 0 < s.limitWeight.density x)
    (z : SpectralRadialObservationSpace R)
    (hz : s.limitPencil ell hl hlR (spectralLowerOrderOperator ell R (hl.trans hlR)
      (spectralRadialWeightMultiplier R s.limitWeight) (spectralRadialWeightMultiplier R a) c ζ
      (spectralFluxBoundary R (s.limitWeight.density R) (a.density R) M)) z=z) :
    ∃ u : SpectralHarmonicPair ell R, u ∈ spectralHarmonicCoreSubspace ell R l ∧
      spectralHarmonicObservation ell R (hl.trans hlR) u=z ∧
      ∃ f g : ℝ → ℂ, Continuous f ∧ Continuous g ∧
        EqOn f (spectralHarmonicRepresentative ell R (hl.trans hlR) u.fst) (Icc δ R) ∧
        EqOn g (spectralHarmonicRepresentative ell R (hl.trans hlR) u.snd) (Icc δ R) ∧
        (deriv f R,deriv g R)=M (f R,g R) := by
  obtain ⟨u,hu,hobs,hweak⟩ := (s.limitPencil_complex_variational ell hl hlR _ z).mp hz
  refine ⟨u,hu,hobs,?_⟩
  apply spectralWeakEquation_robin ell R l δ (hl.trans hlR) hl hlδ hδR
    s.limitWeight a u c ζ M hw ha hwc hac hpos hposc
  simpa only [hobs] using hweak

end DefocusingNLS.SpectralPenaltyFamily

end OAI
