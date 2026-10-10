import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralFirstClosedBoundary
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralClosedClassicalExtension
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralFluxRobin
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralRepresentativeTrace

namespace OAI

/-! The exact variational equation implies the Robin condition on classical endpoint extensions. -/

open Set
namespace DefocusingNLS

theorem spectralWeakEquation_robin (ell : ℕ) (R l δ : ℝ) (hR : 0 < R)
    (hl : 0 < l) (hlδ : l < δ) (hδR : δ < R)
    (w a : SpectralHarmonicWeight R) (u : SpectralHarmonicPair ell R) (c ζ : ℂ)
    (M : ℂ × ℂ →L[ℂ] ℂ × ℂ)
    (hw : ContinuousOn w.density (Ioo 0 R)) (ha : ContinuousOn a.density (Ioo 0 R))
    (hwc : ContinuousOn w.density (Icc δ R)) (hac : ContinuousOn a.density (Icc δ R))
    (hpos : ∀ x ∈ Ioo 0 R, 0 < w.density x) (hposc : ∀ x ∈ Icc δ R, 0 < w.density x)
    (he : ∀ v : spectralHarmonicCoreSubspace ell R l,
      spectralHarmonicPairComplexForm ell R w u v=
      inner ℂ (spectralLowerOrderOperator ell R hR
        (spectralRadialWeightMultiplier R w) (spectralRadialWeightMultiplier R a) c ζ
        (spectralFluxBoundary R (w.density R) (a.density R) M)
        (spectralHarmonicObservation ell R hR u)) v) :
    ∃ f g : ℝ → ℂ, Continuous f ∧ Continuous g ∧
      EqOn f (spectralHarmonicRepresentative ell R hR u.fst) (Icc δ R) ∧
      EqOn g (spectralHarmonicRepresentative ell R hR u.snd) (Icc δ R) ∧
      (deriv f R,deriv g R)=M (f R,g R) := by
  let B := spectralFluxBoundary R (w.density R) (a.density R) M
  obtain ⟨Pf,hPf,_,_,hfluxf,hPfR⟩ := spectralFirst_closedBoundary ell R l δ hR hl hlδ hδR
    w a u c ζ B hw ha hwc hpos he
  obtain ⟨Pg,hPg,_,_,hfluxg,hPgR⟩ := spectralSecond_closedBoundary ell R δ hR
    (hl.trans hlδ) hδR w a u c ζ B hw ha hwc hpos
    (fun t => he ⟨spectralSecondTest ell R t,spectralSecondTest_core ell R l t⟩)
  obtain ⟨f,hf,_,hef,hfR⟩ := spectralSecond_closedExtension ell R δ hR (hl.trans hlδ) hδR
    w (spectralNegWeight a) (spectralSwapPair ell R u) Pf hPf hwc hac.neg hposc hfluxf
  obtain ⟨g,hg,_,heg,hgR⟩ := spectralSecond_closedExtension ell R δ hR (hl.trans hlδ) hδR
    w a u Pg hPg hwc hac hposc hfluxg
  change EqOn f (spectralHarmonicRepresentative ell R hR u.fst) (Icc δ R) at hef
  have hsf : (spectralSwapPair ell R u).fst=u.snd := rfl
  rw [hsf] at hfR
  have hfr : f R=spectralHarmonicRepresentative ell R hR u.fst R := hef ⟨hδR.le,le_rfl⟩
  have hgr : g R=spectralHarmonicRepresentative ell R hR u.snd R := heg ⟨hδR.le,le_rfl⟩
  have htrace : (f R,g R)=spectralHarmonicPairTraces ell R hR u := by
    rw [hfr,hgr]
    exact spectralHarmonicRepresentative_trace ell R hR u
  refine ⟨f,g,hf,hg,hef,heg,?_⟩
  apply (spectralFluxBoundary_condition R (w.density R) (a.density R)
    hR.ne' (hposc R ⟨hδR.le,le_rfl⟩).ne' M (f R,g R) (deriv f R,deriv g R)).mp
  apply Prod.ext
  · change (R : ℂ)^11*((w.density R : ℂ)*deriv f R-(a.density R : ℂ)*g R)=
      (B (f R,g R)).1
    rw [htrace,← hPfR,hgr]
    convert hfR using 1
    simp only [spectralNegWeight,Complex.ofReal_neg,neg_mul,sub_eq_add_neg]
  · change (R : ℂ)^11*((w.density R : ℂ)*deriv g R+(a.density R : ℂ)*f R)=
      (B (f R,g R)).2
    rw [htrace,← hPgR,hfr]
    exact hgR

end DefocusingNLS

end OAI
