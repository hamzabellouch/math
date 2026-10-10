import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralFirstFlux
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralCompactRadialTest
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralInteriorFluxPrimitive

namespace OAI

/-! The first flux has a classical primitive on every exterior annulus. -/

open Set MeasureTheory
open scoped SchwartzMap ContDiff
namespace DefocusingNLS

theorem spectralFirstFlux_primitive (ell : ℕ) (R l α β : ℝ) (hR : 0 < R)
    (hl : 0 < l) (hα : l < α) (hαβ : α < β) (hβ : β < R)
    (w a : SpectralHarmonicWeight R) (u : SpectralHarmonicPair ell R) (c ζ : ℂ)
    (B : ℂ × ℂ →L[ℂ] ℂ × ℂ)
    (hw : ContinuousOn w.density (Ioo 0 R)) (ha : ContinuousOn a.density (Ioo 0 R))
    (he : ∀ v : spectralHarmonicCoreSubspace ell R l,
      spectralHarmonicPairComplexForm ell R w u v=
      inner ℂ (spectralLowerOrderOperator ell R hR
        (spectralRadialWeightMultiplier R w) (spectralRadialWeightMultiplier R a) c ζ B
        (spectralHarmonicObservation ell R hR u)) v) :
    ∃ P : ℝ → ℂ,
      (∀ x ∈ Ioo α β, HasDerivAt P
        (spectralSecondContinuousSource ell R hR w (spectralSwapPair ell R u) (-c) (-ζ) x) x) ∧
      ∀ᵐ x, x ∈ Ioo α β →
        spectralSecondFlux ell R w (spectralNegWeight a) (spectralSwapPair ell R u) x=P x := by
  have hsub : Ioo l R ⊆ Ioo 0 R := fun x hx => ⟨hl.trans hx.1,hx.2⟩
  apply spectralInteriorFlux_primitive l R α β hα hαβ hβ
    (spectralSecondFlux ell R w (spectralNegWeight a) (spectralSwapPair ell R u))
    (spectralSecondContinuousSource ell R hR w (spectralSwapPair ell R u) (-c) (-ζ))
    ((spectralSecondFlux_locallyIntegrableOn ell R w (spectralNegWeight a)
      (spectralSwapPair ell R u) hw ha.neg).mono_set hsub)
    ((spectralSecondContinuousSource_continuousOn ell R hR w
      (spectralSwapPair ell R u) (-c) (-ζ) hw).mono hsub)
  intro φ hφ hφc hφs
  let f := spectralRealSchwartzTest φ hφ hφc
  have hzero (r : ℝ) (hr : r ≤ l) : f r=0 := by
    have hz : φ r=0 := image_eq_zero_of_notMem_tsupport
      (fun h => (not_lt_of_ge hr) (hφs h).1)
    simp only [f,spectralRealSchwartzTest_apply,hz,Complex.ofReal_zero]
  have hφR : φ R=0 := image_eq_zero_of_notMem_tsupport
    (fun h => (lt_irrefl R) (hφs h).2)
  have hfR : f R=0 := by simp only [f,spectralRealSchwartzTest_apply,hφR,Complex.ofReal_zero]
  have ht := spectralFirstBalance_to_flux ell R hR w a u c ζ B f hfR
    (he ⟨spectralFirstTest ell R f,spectralFirstTest_core ell R l f hzero⟩)
  simp only [f,spectralRealSchwartzTest_deriv,spectralRealSchwartzTest_apply,
    Complex.star_def,Complex.conj_ofReal,← Complex.real_smul] at ht
  rw [spectralCompactTest_integral R (deriv φ) _ (tsupport_deriv_subset.trans (hφs.trans hsub)),
    spectralCompactTest_integral R φ _ (hφs.trans hsub)] at ht
  have hs : (∫ x, φ x • spectralSecondSource ell R w (spectralSwapPair ell R u) (-c) (-ζ) x)=
      ∫ x, φ x • spectralSecondContinuousSource ell R hR w
        (spectralSwapPair ell R u) (-c) (-ζ) x := by
    apply integral_congr_ae
    have hae := (ae_restrict_iff' measurableSet_Icc).mp
      (spectralSecondSource_ae ell R hR w (spectralSwapPair ell R u) (-c) (-ζ))
    filter_upwards [hae] with x hx
    by_cases hmem : x ∈ Icc (0 : ℝ) R
    · rw [hx hmem]
    · have hz : φ x=0 := image_eq_zero_of_notMem_tsupport
        (fun h => hmem (Ioo_subset_Icc_self (hsub (hφs h))))
      simp only [hz,zero_smul]
  rwa [hs] at ht

end DefocusingNLS

end OAI
