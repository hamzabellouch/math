import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralClassicalFluxAE
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralClosedSource
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralCutoffFluxTrace
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralEndpointTest
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralBoundaryFlux

namespace OAI

/-! The second scalar weak equation gives its exact classical outer flux trace. -/

open Set MeasureTheory
open scoped SchwartzMap
namespace DefocusingNLS

theorem spectralSecond_closedBoundary (ell : ℕ) (R δ : ℝ) (hR : 0 < R)
    (hδ : 0 < δ) (hδR : δ < R)
    (w a : SpectralHarmonicWeight R) (u : SpectralHarmonicPair ell R) (c ζ : ℂ)
    (B : ℂ × ℂ →L[ℂ] ℂ × ℂ)
    (hw : ContinuousOn w.density (Ioo 0 R)) (ha : ContinuousOn a.density (Ioo 0 R))
    (hwc : ContinuousOn w.density (Icc δ R))
    (hpos : ∀ x ∈ Ioo 0 R, 0 < w.density x)
    (he : ∀ f : 𝓢(ℝ,ℂ),
      spectralHarmonicPairComplexForm ell R w u (spectralSecondTest ell R f)=
      inner ℂ (spectralLowerOrderOperator ell R hR
        (spectralRadialWeightMultiplier R w) (spectralRadialWeightMultiplier R a) c ζ B
        (spectralHarmonicObservation ell R hR u)) (spectralSecondTest ell R f)) :
    ∃ P : ℝ → ℂ, Continuous P ∧
      (∀ x ∈ Icc δ R, HasDerivAt P (spectralSecondContinuousSource ell R hR w u c ζ x) x) ∧
      EqOn (spectralSecondClassicalFlux ell R hR w a u) P (Ioo δ R) ∧
      (∀ᵐ x, x ∈ Icc δ R → spectralSecondFlux ell R w a u x=P x) ∧
      P R=(B (spectralHarmonicPairTraces ell R hR u)).2 := by
  have hs : Ioo δ R ⊆ Ioo 0 R := fun x hx => ⟨hδ.trans hx.1,hx.2⟩
  have hG := spectralSecondContinuousSource_closed ell R δ hR hδ w u c ζ hwc
  have hclass := (spectralSecond_classical ell R hR w a u c ζ B hw ha hpos he).2.2
  have hae := spectralSecondClassicalFlux_ae ell R hR w a u c ζ B hw ha hpos he
  obtain ⟨P,hP,hd,hEq,hFP⟩ := spectralClosedFlux_ae_primitive δ R hδR
    (spectralSecondFlux ell R w a u) (spectralSecondClassicalFlux ell R hR w a u)
    (spectralSecondContinuousSource ell R hR w u c ζ) hG
    (fun x hx => hclass x (hs hx)) (by
      filter_upwards [hae] with x hx hxr
      exact hx (hs hxr))
  refine ⟨P,hP,hd,hEq,hFP,?_⟩
  obtain ⟨f,hfR,hf,hdf⟩ := spectralEndpointTest δ R hδR
  apply spectralCutoffFlux_trace δ R hδ.le hδR
    (spectralSecondFlux ell R w a u) (spectralSecondSource ell R w u c ζ) P
    (spectralSecondContinuousSource ell R hR w u c ζ) hP hG hd hFP _ f hfR hf hdf
    (B (spectralHarmonicPairTraces ell R hR u)).2
  · simpa only [hfR,star_one,one_mul] using spectralSecond_boundaryFlux ell R hR w a u c ζ B f (he f)
  · have hsource := (ae_restrict_iff' measurableSet_Icc).mp (spectralSecondSource_ae ell R hR w u c ζ)
    filter_upwards [hsource] with x hx hxr
    exact hx ⟨hδ.le.trans hxr.1,hxr.2⟩

end DefocusingNLS

end OAI
