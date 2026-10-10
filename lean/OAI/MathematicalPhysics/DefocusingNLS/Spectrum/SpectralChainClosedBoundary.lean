import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralChainBoundaryFlux
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralForcedClosedBoundary
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralClosedSource

namespace OAI

/-! Endpoint flux traces of the genuine constrained first-chain equations. -/

open Set MeasureTheory
open scoped SchwartzMap
namespace DefocusingNLS

theorem spectralSecondChain_closedBoundary (ell : ℕ) (R δ : ℝ) (hR : 0 < R)
    (hδ : 0 < δ) (hδR : δ < R)
    (w a : SpectralHarmonicWeight R) (u₀ u₁ : SpectralHarmonicPair ell R) (c ζ : ℂ)
    (B B' : ℂ × ℂ →L[ℂ] ℂ × ℂ)
    (hw : ContinuousOn w.density (Ioo 0 R)) (ha : ContinuousOn a.density (Ioo 0 R))
    (hwc : ContinuousOn w.density (Icc δ R))
    (hpos : ∀ x ∈ Ioo 0 R, 0 < w.density x)
    (he : ∀ f : 𝓢(ℝ,ℂ),
      spectralHarmonicPairComplexForm ell R w u₁ (spectralSecondTest ell R f) =
      inner ℂ (spectralLowerOrderOperator ell R hR
        (spectralRadialWeightMultiplier R w) (spectralRadialWeightMultiplier R a) c ζ B
        (spectralHarmonicObservation ell R hR u₁) +
        spectralLowerOrderSlope ell R hR (spectralRadialWeightMultiplier R w) B'
          (spectralHarmonicObservation ell R hR u₀)) (spectralSecondTest ell R f)) :
    ∃ P : ℝ → ℂ, Continuous P ∧
      (∀ x ∈ Icc δ R, HasDerivAt P (spectralSecondChainSource ell R hR w u₀ u₁ c ζ x) x) ∧
      EqOn (spectralSecondClassicalFlux ell R hR w a u₁) P (Ioo δ R) ∧
      (∀ᵐ x, x ∈ Icc δ R → spectralSecondFlux ell R w a u₁ x = P x) ∧
      P R = (B (spectralHarmonicPairTraces ell R hR u₁)).2 +
        (B' (spectralHarmonicPairTraces ell R hR u₀)).2 := by
  have hGc : ContinuousOn (spectralSecondChainSource ell R hR w u₀ u₁ c ζ) (Icc δ R) :=
    (spectralSecondContinuousSource_closed ell R δ hR hδ w u₁ c ζ hwc).sub
      ((Complex.continuous_ofReal.continuousOn.pow 11).mul
        (hwc.smul (spectralHarmonicRepresentative_continuousOn_closed ell R δ hR hδ u₀.fst)))
  apply spectralForced_closedBoundary ell 0 R δ le_rfl hR hδ hδR w a u₁ _ _
    hw ha hpos (spectralSecondChainSource_continuousOn ell R hR w u₀ u₁ c ζ hw) hGc
    (spectralSecondFlux_locallyIntegrableOn ell R w a u₁ hw ha)
    (spectralSecondChain_weak_flux ell R hR w a u₀ u₁ c ζ B B' hw he)
  intro f hfR _
  simpa only [hfR,star_one,one_mul] using
    spectralSecondChain_boundary_flux ell R hR w a u₀ u₁ c ζ B B' f (he f)

theorem spectralFirstChain_closedBoundary (ell : ℕ) (L R δ : ℝ) (hR : 0 < R)
    (hL : 0 ≤ L) (hLδ : L < δ) (hδR : δ < R)
    (w a : SpectralHarmonicWeight R) (u₀ u₁ : SpectralHarmonicPair ell R) (c ζ : ℂ)
    (B B' : ℂ × ℂ →L[ℂ] ℂ × ℂ)
    (hw : ContinuousOn w.density (Ioo 0 R)) (ha : ContinuousOn a.density (Ioo 0 R))
    (hwc : ContinuousOn w.density (Icc δ R))
    (hpos : ∀ x ∈ Ioo 0 R, 0 < w.density x)
    (he : ∀ v : spectralHarmonicCoreSubspace ell R L,
      spectralHarmonicPairComplexForm ell R w u₁ v =
      inner ℂ (spectralLowerOrderOperator ell R hR
        (spectralRadialWeightMultiplier R w) (spectralRadialWeightMultiplier R a) c ζ B
        (spectralHarmonicObservation ell R hR u₁) +
        spectralLowerOrderSlope ell R hR (spectralRadialWeightMultiplier R w) B'
          (spectralHarmonicObservation ell R hR u₀)) v) :
    ∃ P : ℝ → ℂ, Continuous P ∧
      (∀ x ∈ Icc δ R, HasDerivAt P (spectralFirstChainSource ell R hR w u₀ u₁ c ζ x) x) ∧
      EqOn (spectralSecondClassicalFlux ell R hR w (spectralNegWeight a) (spectralSwapPair ell R u₁))
        P (Ioo δ R) ∧
      (∀ᵐ x, x ∈ Icc δ R →
        spectralSecondFlux ell R w (spectralNegWeight a) (spectralSwapPair ell R u₁) x = P x) ∧
      P R = (B (spectralHarmonicPairTraces ell R hR u₁)).1 +
        (B' (spectralHarmonicPairTraces ell R hR u₀)).1 := by
  have hδ : 0 < δ := hL.trans_lt hLδ
  have hs : Ioo L R ⊆ Ioo 0 R := fun x hx => ⟨hL.trans_lt hx.1,hx.2⟩
  have hGc : ContinuousOn (spectralFirstChainSource ell R hR w u₀ u₁ c ζ) (Icc δ R) :=
    (spectralSecondContinuousSource_closed ell R δ hR hδ w
      (spectralSwapPair ell R u₁) (-c) (-ζ) hwc).add
      ((Complex.continuous_ofReal.continuousOn.pow 11).mul
        (hwc.smul (spectralHarmonicRepresentative_continuousOn_closed ell R δ hR hδ u₀.snd)))
  apply spectralForced_closedBoundary ell L R δ hL hR hLδ hδR
    w (spectralNegWeight a) (spectralSwapPair ell R u₁) _ _
    (hw.mono hs) (ha.neg.mono hs) (fun x hx => hpos x (hs hx))
    ((spectralFirstChainSource_continuousOn ell R hR w u₀ u₁ c ζ hw).mono hs) hGc
    ((spectralSecondFlux_locallyIntegrableOn ell R w (spectralNegWeight a)
      (spectralSwapPair ell R u₁) hw ha.neg).mono_set hs)
    (spectralFirstChain_weak_flux ell L R hL hR w a u₀ u₁ c ζ B B' hw he)
  intro f hfR hf
  have ht := he ⟨spectralFirstTest ell R f,spectralFirstTest_core ell R L f
    (fun x hx => hf x (hx.trans hLδ.le))⟩
  simpa only [hfR,star_one,one_mul] using
    spectralFirstChain_boundary_flux ell R hR w a u₀ u₁ c ζ B B' f ht

end DefocusingNLS

end OAI
