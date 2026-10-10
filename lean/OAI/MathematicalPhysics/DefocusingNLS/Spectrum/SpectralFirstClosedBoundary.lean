import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralSecondClosedBoundary

namespace OAI

/-! Exterior first-component tests give the remaining outer flux trace. -/

open Set MeasureTheory
open scoped SchwartzMap
namespace DefocusingNLS

theorem spectralFirst_closedBoundary (ell : ℕ) (R l δ : ℝ) (hR : 0 < R)
    (hl : 0 < l) (hlδ : l < δ) (hδR : δ < R)
    (w a : SpectralHarmonicWeight R) (u : SpectralHarmonicPair ell R) (c ζ : ℂ)
    (B : ℂ × ℂ →L[ℂ] ℂ × ℂ)
    (hw : ContinuousOn w.density (Ioo 0 R)) (ha : ContinuousOn a.density (Ioo 0 R))
    (hwc : ContinuousOn w.density (Icc δ R))
    (hpos : ∀ x ∈ Ioo 0 R, 0 < w.density x)
    (he : ∀ v : spectralHarmonicCoreSubspace ell R l,
      spectralHarmonicPairComplexForm ell R w u v=
      inner ℂ (spectralLowerOrderOperator ell R hR
        (spectralRadialWeightMultiplier R w) (spectralRadialWeightMultiplier R a) c ζ B
        (spectralHarmonicObservation ell R hR u)) v) :
    ∃ P : ℝ → ℂ, Continuous P ∧
      (∀ x ∈ Icc δ R, HasDerivAt P
        (spectralSecondContinuousSource ell R hR w (spectralSwapPair ell R u) (-c) (-ζ) x) x) ∧
      EqOn (spectralSecondClassicalFlux ell R hR w (spectralNegWeight a) (spectralSwapPair ell R u)) P
        (Ioo δ R) ∧
      (∀ᵐ x, x ∈ Icc δ R →
        spectralSecondFlux ell R w (spectralNegWeight a) (spectralSwapPair ell R u) x=P x) ∧
      P R=(B (spectralHarmonicPairTraces ell R hR u)).1 := by
  have hs : Ioo δ R ⊆ Ioo l R := fun x hx => ⟨hlδ.trans hx.1,hx.2⟩
  have hG := spectralSecondContinuousSource_closed ell R δ hR (hl.trans hlδ)
    w (spectralSwapPair ell R u) (-c) (-ζ) hwc
  have hclass := (spectralFirst_classical ell R l hR hl w a u c ζ B hw ha hpos he).2.2
  have hae := spectralFirstClassicalFlux_ae ell R l hR hl w a u c ζ B hw ha hpos he
  obtain ⟨P,hP,hd,hEq,hFP⟩ := spectralClosedFlux_ae_primitive δ R hδR
    (spectralSecondFlux ell R w (spectralNegWeight a) (spectralSwapPair ell R u))
    (spectralSecondClassicalFlux ell R hR w (spectralNegWeight a) (spectralSwapPair ell R u))
    (spectralSecondContinuousSource ell R hR w (spectralSwapPair ell R u) (-c) (-ζ)) hG
    (fun x hx => hclass x (hs hx)) (by
      filter_upwards [hae] with x hx hxr
      exact hx (hs hxr))
  refine ⟨P,hP,hd,hEq,hFP,?_⟩
  obtain ⟨f,hfR,hf,hdf⟩ := spectralEndpointTest δ R hδR
  apply spectralCutoffFlux_trace δ R (hl.trans hlδ).le hδR
    (spectralSecondFlux ell R w (spectralNegWeight a) (spectralSwapPair ell R u))
    (spectralSecondSource ell R w (spectralSwapPair ell R u) (-c) (-ζ)) P
    (spectralSecondContinuousSource ell R hR w (spectralSwapPair ell R u) (-c) (-ζ))
    hP hG hd hFP _ f hfR hf hdf (B (spectralHarmonicPairTraces ell R hR u)).1
  · have ht := he ⟨spectralFirstTest ell R f,spectralFirstTest_core ell R l f
      (fun x hx => hf x (hx.trans hlδ.le))⟩
    simpa only [hfR,star_one,one_mul] using
      spectralFirstBoundaryBalance_to_flux ell R hR w a u c ζ B f ht
  · have hsource := (ae_restrict_iff' measurableSet_Icc).mp
      (spectralSecondSource_ae ell R hR w (spectralSwapPair ell R u) (-c) (-ζ))
    filter_upwards [hsource] with x hx hxr
    exact hx ⟨(hl.trans hlδ).le.trans hxr.1,hxr.2⟩

end DefocusingNLS

end OAI
