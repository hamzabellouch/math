import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralChainClosedBoundary
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralFluxBoundaryDerivative
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralClosedExtensionRegularity
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralFluxRobin
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralRepresentativeTrace

namespace OAI

/-! The exact variational equation gives a Robin extension with continuous endpoint derivatives. -/

open Set
namespace DefocusingNLS

theorem spectralWeakChain_robin_C1 (ell : ℕ) (R l δ : ℝ) (hR : 0 < R)
    (hl : 0 < l) (hlδ : l < δ) (hδR : δ < R)
    (w a : SpectralHarmonicWeight R) (u₀ u₁ : SpectralHarmonicPair ell R) (c ζ : ℂ)
    (M M' : ℂ × ℂ →L[ℂ] ℂ × ℂ)
    (hw : ContinuousOn w.density (Ioo 0 R)) (ha : ContinuousOn a.density (Ioo 0 R))
    (hwc : ContinuousOn w.density (Icc δ R)) (hac : ContinuousOn a.density (Icc δ R))
    (hpos : ∀ x ∈ Ioo 0 R, 0 < w.density x) (hposc : ∀ x ∈ Icc δ R, 0 < w.density x)
    (he : ∀ v : spectralHarmonicCoreSubspace ell R l,
      spectralHarmonicPairComplexForm ell R w u₁ v=
      inner ℂ (spectralLowerOrderOperator ell R hR
        (spectralRadialWeightMultiplier R w) (spectralRadialWeightMultiplier R a) c ζ
        (spectralFluxBoundary R (w.density R) (a.density R) M)
        (spectralHarmonicObservation ell R hR u₁) +
        spectralLowerOrderSlope ell R hR (spectralRadialWeightMultiplier R w)
          (spectralFluxBoundarySlope R (w.density R) M')
          (spectralHarmonicObservation ell R hR u₀)) v) :
    ∃ f g : ℝ → ℂ, Continuous f ∧ Continuous g ∧
      ContinuousOn (deriv f) (Icc δ R) ∧ ContinuousOn (deriv g) (Icc δ R) ∧
      EqOn f (spectralHarmonicRepresentative ell R hR u₁.fst) (Icc δ R) ∧
      EqOn g (spectralHarmonicRepresentative ell R hR u₁.snd) (Icc δ R) ∧
      (deriv f R,deriv g R)=M (f R,g R) + M' (spectralHarmonicPairTraces ell R hR u₀) := by
  let B := spectralFluxBoundary R (w.density R) (a.density R) M
  let B' := spectralFluxBoundarySlope R (w.density R) M'
  obtain ⟨Pf,hPf,_,_,hfluxf,hPfR⟩ := spectralFirstChain_closedBoundary ell l R δ hR hl.le hlδ hδR
    w a u₀ u₁ c ζ B B' hw ha hwc hpos he
  obtain ⟨Pg,hPg,_,_,hfluxg,hPgR⟩ := spectralSecondChain_closedBoundary ell R δ hR
    (hl.trans hlδ) hδR w a u₀ u₁ c ζ B B' hw ha hwc hpos
    (fun t => he ⟨spectralSecondTest ell R t,spectralSecondTest_core ell R l t⟩)
  obtain ⟨f,hf,hdf,_,hef,hfR⟩ := spectralSecond_closedExtension_C1 ell R δ hR (hl.trans hlδ) hδR
    w (spectralNegWeight a) (spectralSwapPair ell R u₁) Pf hPf hwc hac.neg hposc hfluxf
  obtain ⟨g,hg,hdg,_,heg,hgR⟩ := spectralSecond_closedExtension_C1 ell R δ hR (hl.trans hlδ) hδR
    w a u₁ Pg hPg hwc hac hposc hfluxg
  change EqOn f (spectralHarmonicRepresentative ell R hR u₁.fst) (Icc δ R) at hef
  have hsf : (spectralSwapPair ell R u₁).fst=u₁.snd := rfl
  rw [hsf] at hfR
  have hfr : f R=spectralHarmonicRepresentative ell R hR u₁.fst R := hef ⟨hδR.le,le_rfl⟩
  have hgr : g R=spectralHarmonicRepresentative ell R hR u₁.snd R := heg ⟨hδR.le,le_rfl⟩
  have htrace : (f R,g R)=spectralHarmonicPairTraces ell R hR u₁ := by
    rw [hfr,hgr]
    exact spectralHarmonicRepresentative_trace ell R hR u₁
  refine ⟨f,g,hf,hg,hdf,hdg,hef,heg,?_⟩
  apply (spectralFluxBoundary_chain_condition R (w.density R) (a.density R)
    hR.ne' (hposc R ⟨hδR.le,le_rfl⟩).ne' M M' (spectralHarmonicPairTraces ell R hR u₀) (f R,g R) (deriv f R,deriv g R)).mp
  apply Prod.ext
  · change (R : ℂ)^11*((w.density R : ℂ)*deriv f R-(a.density R : ℂ)*g R)=
      (B (f R,g R)).1 + (B' (spectralHarmonicPairTraces ell R hR u₀)).1
    rw [htrace,← hPfR,hgr]
    convert hfR using 1
    simp only [spectralNegWeight,Complex.ofReal_neg,neg_mul,sub_eq_add_neg]
  · change (R : ℂ)^11*((w.density R : ℂ)*deriv g R+(a.density R : ℂ)*f R)=
      (B (f R,g R)).2 + (B' (spectralHarmonicPairTraces ell R hR u₀)).2
    rw [htrace,← hPgR,hfr]
    exact hgR

end DefocusingNLS

end OAI
