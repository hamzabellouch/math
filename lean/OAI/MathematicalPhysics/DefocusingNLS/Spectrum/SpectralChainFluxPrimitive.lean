import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralChainFluxBalance
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralForcedClassicalFlux

namespace OAI

/-! The weak first-chain load has a continuous radial source and therefore
produces classical fluxes across the core interface. -/

open Set MeasureTheory Filter Topology
open scoped SchwartzMap ContDiff
namespace DefocusingNLS

theorem spectralCompactTest_integrable (R : ℝ) (φ : ℝ → ℝ)
    (hφ : Continuous φ) (hc : HasCompactSupport φ) (hS : tsupport φ ⊆ Ioo 0 R)
    (G : ℝ → ℂ) (hG : ContinuousOn G (Ioo 0 R)) :
    Integrable (fun (x : ℝ) => φ x • G x) := by
  have hi : IntegrableOn (fun (x : ℝ) => φ x • G x) (tsupport φ) :=
    (hφ.continuousOn.smul (hG.mono hS)).integrableOn_compact hc
  have he : (tsupport φ).indicator (fun (x : ℝ) => φ x • G x) = (fun (x : ℝ) => φ x • G x) := by
    funext x
    by_cases hx : x ∈ tsupport φ
    · exact indicator_of_mem hx _
    · rw [indicator_of_notMem hx, image_eq_zero_of_notMem_tsupport hx, zero_smul]
  rw [← he]
  exact (integrable_indicator_iff hc.isClosed.measurableSet).mpr hi

noncomputable def spectralSecondChainSource (ell : ℕ) (R : ℝ) (hR : 0 < R)
    (w : SpectralHarmonicWeight R) (u₀ u₁ : SpectralHarmonicPair ell R)
    (c ζ : ℂ) (x : ℝ) : ℂ :=
  spectralSecondContinuousSource ell R hR w u₁ c ζ x -
    (x : ℂ)^11 * (w.density x • spectralHarmonicRepresentative ell R hR u₀.fst x)

theorem spectralSecondChainSource_continuousOn (ell : ℕ) (R : ℝ) (hR : 0 < R)
    (w : SpectralHarmonicWeight R) (u₀ u₁ : SpectralHarmonicPair ell R)
    (c ζ : ℂ) (hw : ContinuousOn w.density (Ioo 0 R)) :
    ContinuousOn (spectralSecondChainSource ell R hR w u₀ u₁ c ζ) (Ioo 0 R) :=
  (spectralSecondContinuousSource_continuousOn ell R hR w u₁ c ζ hw).sub
    ((Complex.continuous_ofReal.continuousOn.pow 11).mul
      (hw.smul (spectralHarmonicRepresentative_continuousOn ell R hR u₀.fst)))

theorem spectralSecondChain_weak_flux (ell : ℕ) (R : ℝ) (hR : 0 < R)
    (w a : SpectralHarmonicWeight R) (u₀ u₁ : SpectralHarmonicPair ell R) (c ζ : ℂ)
    (B B' : ℂ × ℂ →L[ℂ] ℂ × ℂ)
    (hw : ContinuousOn w.density (Ioo 0 R))
    (he : ∀ f : 𝓢(ℝ,ℂ),
      spectralHarmonicPairComplexForm ell R w u₁ (spectralSecondTest ell R f) =
      inner ℂ (spectralLowerOrderOperator ell R hR
        (spectralRadialWeightMultiplier R w) (spectralRadialWeightMultiplier R a) c ζ B
        (spectralHarmonicObservation ell R hR u₁) +
        spectralLowerOrderSlope ell R hR (spectralRadialWeightMultiplier R w) B'
          (spectralHarmonicObservation ell R hR u₀)) (spectralSecondTest ell R f))
    (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hφs : tsupport φ ⊆ Ioo 0 R) :
    (∫ x, deriv φ x • spectralSecondFlux ell R w a u₁ x) =
      -(∫ x, φ x • spectralSecondChainSource ell R hR w u₀ u₁ c ζ x) := by
  let f := spectralRealSchwartzTest φ hφ hφc
  have hφR : φ R = 0 := image_eq_zero_of_notMem_tsupport
    (fun h => (lt_irrefl R) (hφs h).2)
  have hfR : f R = 0 := by simp only [f, spectralRealSchwartzTest_apply, hφR, Complex.ofReal_zero]
  have hb := spectralSecondChain_flux_balance ell R hR w a u₀ u₁ c ζ B B' f hfR (he f)
  simp only [f, spectralRealSchwartzTest_deriv, spectralRealSchwartzTest_apply,
    Complex.star_def, Complex.conj_ofReal] at hb
  have hreorder : (fun (x : ℝ) => (x : ℂ)^11 * ((φ x : ℂ) *
      (w.density x • spectralHarmonicValue ell R u₀.fst x))) =
      (fun (x : ℝ) => φ x • ((x : ℂ)^11 *
        (w.density x • spectralHarmonicValue ell R u₀.fst x))) := by
    funext x
    simp only [Complex.real_smul]
    ring
  rw [hreorder] at hb
  simp only [← Complex.real_smul] at hb
  rw [spectralCompactTest_integral R (deriv φ) _ (tsupport_deriv_subset.trans hφs),
    spectralCompactTest_integral R φ _ hφs, spectralCompactTest_integral R φ _ hφs] at hb
  have hsrc : (∫ x, φ x • spectralSecondSource ell R w u₁ c ζ x) =
      ∫ x, φ x • spectralSecondContinuousSource ell R hR w u₁ c ζ x := by
    apply integral_congr_ae
    have hae := (ae_restrict_iff' measurableSet_Icc).mp (spectralSecondSource_ae ell R hR w u₁ c ζ)
    filter_upwards [hae] with x hx
    by_cases hm : x ∈ Icc (0 : ℝ) R
    · rw [hx hm]
    · rw [image_eq_zero_of_notMem_tsupport (fun h => hm (Ioo_subset_Icc_self (hφs h)))]
      simp only [zero_smul]
  have hforce : (∫ x, φ x • ((x : ℂ)^11 *
      (w.density x • spectralHarmonicValue ell R u₀.fst x))) =
      ∫ x, φ x • ((x : ℂ)^11 *
        (w.density x • spectralHarmonicRepresentative ell R hR u₀.fst x)) := by
    apply integral_congr_ae
    have hae := (ae_restrict_iff' measurableSet_Icc).mp
      (spectralHarmonicRepresentative_ae ell R hR u₀.fst)
    filter_upwards [hae] with x hx
    by_cases hm : x ∈ Icc (0 : ℝ) R
    · rw [hx hm]
    · rw [image_eq_zero_of_notMem_tsupport (fun h => hm (Ioo_subset_Icc_self (hφs h)))]
      simp only [zero_smul]
  rw [hsrc, hforce] at hb
  have hSc := spectralSecondContinuousSource_continuousOn ell R hR w u₁ c ζ hw
  have hFc : ContinuousOn (fun (x : ℝ) => (x : ℂ)^11 *
      (w.density x • spectralHarmonicRepresentative ell R hR u₀.fst x)) (Ioo 0 R) :=
    (Complex.continuous_ofReal.continuousOn.pow 11).mul
    (hw.smul (spectralHarmonicRepresentative_continuousOn ell R hR u₀.fst))
  have hiS := spectralCompactTest_integrable R φ hφ.continuous hφc hφs _ hSc
  have hiF := spectralCompactTest_integrable R φ hφ.continuous hφc hφs _ hFc
  have hsplit : (fun (x : ℝ) => φ x • spectralSecondChainSource ell R hR w u₀ u₁ c ζ x) =
      (fun (x : ℝ) => φ x • spectralSecondContinuousSource ell R hR w u₁ c ζ x) -
      (fun (x : ℝ) => φ x • ((x : ℂ)^11 *
        (w.density x • spectralHarmonicRepresentative ell R hR u₀.fst x))) := by
    funext x
    exact smul_sub _ _ _
  rw [hsplit]
  change (∫ x, deriv φ x • spectralSecondFlux ell R w a u₁ x) =
    -(∫ x, φ x • spectralSecondContinuousSource ell R hR w u₁ c ζ x -
      φ x • ((x : ℂ)^11 * (w.density x • spectralHarmonicRepresentative ell R hR u₀.fst x)))
  rw [integral_sub hiS hiF]
  linear_combination hb

theorem spectralSecondChain_classical (ell : ℕ) (R : ℝ) (hR : 0 < R)
    (w a : SpectralHarmonicWeight R) (u₀ u₁ : SpectralHarmonicPair ell R) (c ζ : ℂ)
    (B B' : ℂ × ℂ →L[ℂ] ℂ × ℂ)
    (hw : ContinuousOn w.density (Ioo 0 R)) (ha : ContinuousOn a.density (Ioo 0 R))
    (hpos : ∀ x ∈ Ioo 0 R, 0 < w.density x)
    (he : ∀ f : 𝓢(ℝ,ℂ),
      spectralHarmonicPairComplexForm ell R w u₁ (spectralSecondTest ell R f) =
      inner ℂ (spectralLowerOrderOperator ell R hR
        (spectralRadialWeightMultiplier R w) (spectralRadialWeightMultiplier R a) c ζ B
        (spectralHarmonicObservation ell R hR u₁) +
        spectralLowerOrderSlope ell R hR (spectralRadialWeightMultiplier R w) B'
          (spectralHarmonicObservation ell R hR u₀)) (spectralSecondTest ell R f)) :
    DifferentiableOn ℝ (spectralHarmonicRepresentative ell R hR u₁.snd) (Ioo 0 R) ∧
      ContinuousOn (deriv (spectralHarmonicRepresentative ell R hR u₁.snd)) (Ioo 0 R) ∧
      ∀ x ∈ Ioo 0 R, HasDerivAt (spectralSecondClassicalFlux ell R hR w a u₁)
        (spectralSecondChainSource ell R hR w u₀ u₁ c ζ x) x := by
  exact spectralSecond_forced_classical ell R hR w a u₁ _ hw ha hpos
    (spectralSecondChainSource_continuousOn ell R hR w u₀ u₁ c ζ hw)
    (spectralSecondChain_weak_flux ell R hR w a u₀ u₁ c ζ B B' hw he)

end DefocusingNLS

end OAI
