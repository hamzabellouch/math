import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralFirstClassicalFlux

namespace OAI

/-! The classical flux agrees almost everywhere with the original completed flux. -/

open Set MeasureTheory
open scoped SchwartzMap
namespace DefocusingNLS

theorem spectralLocalFlux_classical_ae (ell : ℕ) (R l r : ℝ) (hR : 0 < R)
    (hl : 0 < l) (hr : r ≤ R) (w a : SpectralHarmonicWeight R)
    (u : SpectralHarmonicPair ell R) (P : ℝ → ℂ)
    (hw : ContinuousOn w.density (Ioo l r)) (ha : ContinuousOn a.density (Ioo l r))
    (hpos : ∀ x ∈ Ioo l r, 0 < w.density x) (hP : ContinuousOn P (Ioo l r))
    (hflux : ∀ᵐ x, x ∈ Ioo l r → spectralSecondFlux ell R w a u x=P x) :
    ∀ᵐ x, x ∈ Ioo l r →
      spectralSecondFlux ell R w a u x=spectralSecondClassicalFlux ell R hR w a u x := by
  filter_upwards [hflux] with x hx hxr
  rw [hx hxr]
  exact (spectralSecondClassicalFlux_eq ell R hR w a u P x (hl.trans hxr.1).ne'
    (hpos x hxr).ne' (spectralSecondFlux_hasDerivAt ell R l r hR hl hr w a u P
      hw ha hpos hP hflux x hxr)).symm

theorem spectralSecondClassicalFlux_ae (ell : ℕ) (R : ℝ) (hR : 0 < R)
    (w a : SpectralHarmonicWeight R) (u : SpectralHarmonicPair ell R) (c ζ : ℂ)
    (B : ℂ × ℂ →L[ℂ] ℂ × ℂ)
    (hw : ContinuousOn w.density (Ioo 0 R)) (ha : ContinuousOn a.density (Ioo 0 R))
    (hpos : ∀ x ∈ Ioo 0 R, 0 < w.density x)
    (he : ∀ f : 𝓢(ℝ,ℂ),
      spectralHarmonicPairComplexForm ell R w u (spectralSecondTest ell R f)=
      inner ℂ (spectralLowerOrderOperator ell R hR
        (spectralRadialWeightMultiplier R w) (spectralRadialWeightMultiplier R a) c ζ B
        (spectralHarmonicObservation ell R hR u)) (spectralSecondTest ell R f)) :
    ∀ᵐ x, x ∈ Ioo 0 R →
      spectralSecondFlux ell R w a u x=spectralSecondClassicalFlux ell R hR w a u x := by
  apply ae_of_mem_of_ae_of_mem_inter_Ioo
  intro l r hl hr hlr
  obtain ⟨P,hP,hflux⟩ := spectralSecondFlux_primitive ell R l r hR hl.1 hlr hr.2 w a u c ζ B hw ha he
  have hs : Ioo l r ⊆ Ioo 0 R := fun x hx => ⟨hl.1.trans hx.1,hx.2.trans hr.2⟩
  have hlocal := spectralLocalFlux_classical_ae ell R l r hR hl.1 hr.2.le w a u P
    (hw.mono hs) (ha.mono hs) (fun x hx => hpos x (hs hx))
    (fun x hx => (hP x hx).continuousAt.continuousWithinAt) hflux
  filter_upwards [hlocal] with x hx hxr
  exact hx hxr.2

theorem spectralFirstClassicalFlux_ae (ell : ℕ) (R l : ℝ) (hR : 0 < R) (hl : 0 < l)
    (w a : SpectralHarmonicWeight R) (u : SpectralHarmonicPair ell R) (c ζ : ℂ)
    (B : ℂ × ℂ →L[ℂ] ℂ × ℂ)
    (hw : ContinuousOn w.density (Ioo 0 R)) (ha : ContinuousOn a.density (Ioo 0 R))
    (hpos : ∀ x ∈ Ioo 0 R, 0 < w.density x)
    (he : ∀ v : spectralHarmonicCoreSubspace ell R l,
      spectralHarmonicPairComplexForm ell R w u v=
      inner ℂ (spectralLowerOrderOperator ell R hR
        (spectralRadialWeightMultiplier R w) (spectralRadialWeightMultiplier R a) c ζ B
        (spectralHarmonicObservation ell R hR u)) v) :
    ∀ᵐ x, x ∈ Ioo l R →
      spectralSecondFlux ell R w (spectralNegWeight a) (spectralSwapPair ell R u) x=
        spectralSecondClassicalFlux ell R hR w (spectralNegWeight a) (spectralSwapPair ell R u) x := by
  apply ae_of_mem_of_ae_of_mem_inter_Ioo
  intro α β hα hβ hαβ
  obtain ⟨P,hP,hflux⟩ := spectralFirstFlux_primitive ell R l α β hR hl hα.1 hαβ hβ.2 w a u c ζ B hw ha he
  have hs : Ioo α β ⊆ Ioo 0 R := fun x hx => ⟨(hl.trans hα.1).trans hx.1,hx.2.trans hβ.2⟩
  have hlocal := spectralLocalFlux_classical_ae ell R α β hR (hl.trans hα.1) hβ.2.le
    w (spectralNegWeight a) (spectralSwapPair ell R u) P
    (hw.mono hs) (ha.neg.mono hs) (fun x hx => hpos x (hs hx))
    (fun x hx => (hP x hx).continuousAt.continuousWithinAt) hflux
  filter_upwards [hlocal] with x hx hxr
  exact hx hxr.2

end DefocusingNLS

end OAI
