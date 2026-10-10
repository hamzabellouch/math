import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralSecondFluxDerivative

namespace OAI

/-! Classical local flux and derivative for every limiting compact-pencil kernel vector. -/

open Set MeasureTheory
namespace DefocusingNLS.SpectralPenaltyFamily
variable {R l : ℝ}

theorem limitPencil_classical_second (s : SpectralPenaltyFamily R l) (ell : ℕ)
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
      ∀ α β : ℝ, 0 < α → α < β → β < R → ∃ P : ℝ → ℂ,
        (∀ x ∈ Ioo α β, HasDerivAt P
          (spectralSecondContinuousSource ell R (hl.trans hlR) s.limitWeight u c ζ x) x) ∧
        (∀ x ∈ Ioo α β,
          HasDerivAt (spectralHarmonicRepresentative ell R (hl.trans hlR) u.snd)
            (spectralSecondDerivativeValue ell R (hl.trans hlR) s.limitWeight a u P x) x) ∧
        ∀ᵐ x, x ∈ Ioo α β → spectralSecondFlux ell R s.limitWeight a u x=P x := by
  obtain ⟨u,hu,hobs,hweak⟩ := (s.limitPencil_complex_variational ell hl hlR _ z).mp hz
  refine ⟨u,hu,hobs,fun α β hα hαβ hβ => ?_⟩
  obtain ⟨P,hP,hflux⟩ := spectralSecondFlux_primitive ell R α β (hl.trans hlR)
    hα hαβ hβ s.limitWeight a u c ζ B hw ha (by
      intro f
      simpa only [hobs] using
        hweak ⟨spectralSecondTest ell R f,spectralSecondTest_core ell R l f⟩)
  refine ⟨P,hP,?_,hflux⟩
  have hsub : Ioo α β ⊆ Ioo 0 R := fun x hx => ⟨hα.trans hx.1,hx.2.trans hβ⟩
  intro x hx
  exact spectralSecondFlux_hasDerivAt ell R α β (hl.trans hlR) hα hβ.le
    s.limitWeight a u P (hw.mono hsub) (ha.mono hsub)
    (fun t ht => hpos t (hsub ht))
    (fun t ht => (hP t ht).continuousAt.continuousWithinAt) hflux x hx

end DefocusingNLS.SpectralPenaltyFamily

end OAI
