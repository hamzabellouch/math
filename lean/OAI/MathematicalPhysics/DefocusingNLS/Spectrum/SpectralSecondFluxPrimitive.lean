import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralSecondFluxRegularity
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralCompactRadialTest
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralLocalFluxPrimitive

namespace OAI

/-! The actual second weak equation gives a continuous flux across every interior radius. -/

open Set MeasureTheory
open scoped SchwartzMap ContDiff
namespace DefocusingNLS

theorem spectralSecondFlux_primitive (ell : ℕ) (R l r : ℝ) (hR : 0 < R)
    (hl : 0 < l) (hlr : l < r) (hr : r < R)
    (w a : SpectralHarmonicWeight R) (u : SpectralHarmonicPair ell R) (c ζ : ℂ)
    (B : ℂ × ℂ →L[ℂ] ℂ × ℂ)
    (hw : ContinuousOn w.density (Ioo 0 R)) (ha : ContinuousOn a.density (Ioo 0 R))
    (he : ∀ f : 𝓢(ℝ,ℂ),
      spectralHarmonicPairComplexForm ell R w u (spectralSecondTest ell R f)=
      inner ℂ (spectralLowerOrderOperator ell R hR
        (spectralRadialWeightMultiplier R w) (spectralRadialWeightMultiplier R a) c ζ B
        (spectralHarmonicObservation ell R hR u)) (spectralSecondTest ell R f)) :
    ∃ P : ℝ → ℂ,
      (∀ x ∈ Ioo l r, HasDerivAt P (spectralSecondContinuousSource ell R hR w u c ζ x) x) ∧
      ∀ᵐ x, x ∈ Ioo l r → spectralSecondFlux ell R w a u x=P x := by
  apply spectralLocalFlux_primitive R l r hl hlr hr
    (spectralSecondFlux ell R w a u) (spectralSecondContinuousSource ell R hR w u c ζ)
    (spectralSecondFlux_locallyIntegrableOn ell R w a u hw ha)
    (spectralSecondContinuousSource_continuousOn ell R hR w u c ζ hw)
  intro φ hφ hφc hφs
  let f := spectralRealSchwartzTest φ hφ hφc
  have hφR : φ R=0 := image_eq_zero_of_notMem_tsupport
    (fun h => (lt_irrefl R) (hφs h).2)
  have hfR : f R=0 := by simp only [f,spectralRealSchwartzTest_apply,hφR,Complex.ofReal_zero]
  have hbal := spectralSecondTest_balance ell R hR w a u c ζ B f hfR (he f)
  have ht := spectralSecondBalance_to_flux ell R hR w a u c ζ f hbal
  simp only [f,spectralRealSchwartzTest_deriv,spectralRealSchwartzTest_apply,
    Complex.star_def,Complex.conj_ofReal,← Complex.real_smul] at ht
  rw [spectralCompactTest_integral R (deriv φ) _ (tsupport_deriv_subset.trans hφs),
    spectralCompactTest_integral R φ _ hφs] at ht
  have hs : (∫ x, φ x • spectralSecondSource ell R w u c ζ x)=
      ∫ x, φ x • spectralSecondContinuousSource ell R hR w u c ζ x := by
    apply integral_congr_ae
    have hae := (ae_restrict_iff' measurableSet_Icc).mp
      (spectralSecondSource_ae ell R hR w u c ζ)
    filter_upwards [hae] with x hx
    by_cases hmem : x ∈ Icc (0 : ℝ) R
    · rw [hx hmem]
    · have hz : φ x=0 := image_eq_zero_of_notMem_tsupport
        (fun h => hmem (Ioo_subset_Icc_self (hφs h)))
      simp only [hz,zero_smul]
  rwa [hs] at ht

end DefocusingNLS

end OAI
