import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralChainFirstBalance
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralChainFluxPrimitive
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralAnnulusClassicalFlux
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralForcedClassicalFlux

namespace OAI

/-! The weak first-chain load has a continuous radial source and therefore
produces classical fluxes across the core interface. -/

open Set MeasureTheory Filter Topology
open scoped SchwartzMap ContDiff
namespace DefocusingNLS

noncomputable def spectralFirstChainSource (ell : ℕ) (R : ℝ) (hR : 0 < R)
    (w : SpectralHarmonicWeight R) (u₀ u₁ : SpectralHarmonicPair ell R)
    (c ζ : ℂ) (x : ℝ) : ℂ :=
  spectralSecondContinuousSource ell R hR w (spectralSwapPair ell R u₁) (-c) (-ζ) x +
    (x : ℂ)^11 * (w.density x • spectralHarmonicRepresentative ell R hR u₀.snd x)

theorem spectralFirstChainSource_continuousOn (ell : ℕ) (R : ℝ) (hR : 0 < R)
    (w : SpectralHarmonicWeight R) (u₀ u₁ : SpectralHarmonicPair ell R)
    (c ζ : ℂ) (hw : ContinuousOn w.density (Ioo 0 R)) :
    ContinuousOn (spectralFirstChainSource ell R hR w u₀ u₁ c ζ) (Ioo 0 R) :=
  (spectralSecondContinuousSource_continuousOn ell R hR w (spectralSwapPair ell R u₁) (-c) (-ζ) hw).add
    ((Complex.continuous_ofReal.continuousOn.pow 11).mul
      (hw.smul (spectralHarmonicRepresentative_continuousOn ell R hR u₀.snd)))

theorem spectralFirstChain_weak_flux (ell : ℕ) (L R : ℝ) (hL : 0 ≤ L) (hR : 0 < R)
    (w a : SpectralHarmonicWeight R) (u₀ u₁ : SpectralHarmonicPair ell R) (c ζ : ℂ)
    (B B' : ℂ × ℂ →L[ℂ] ℂ × ℂ)
    (hw : ContinuousOn w.density (Ioo 0 R))
    (he : ∀ v : spectralHarmonicCoreSubspace ell R L,
      spectralHarmonicPairComplexForm ell R w u₁ v =
      inner ℂ (spectralLowerOrderOperator ell R hR
        (spectralRadialWeightMultiplier R w) (spectralRadialWeightMultiplier R a) c ζ B
        (spectralHarmonicObservation ell R hR u₁) +
        spectralLowerOrderSlope ell R hR (spectralRadialWeightMultiplier R w) B'
          (spectralHarmonicObservation ell R hR u₀)) v)
    (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hφs : tsupport φ ⊆ Ioo L R) :
    (∫ x, deriv φ x • spectralSecondFlux ell R w (spectralNegWeight a) (spectralSwapPair ell R u₁) x) =
      -(∫ x, φ x • spectralFirstChainSource ell R hR w u₀ u₁ c ζ x) := by
  let f := spectralRealSchwartzTest φ hφ hφc
  have hφR : φ R = 0 := image_eq_zero_of_notMem_tsupport
    (fun h => (lt_irrefl R) (hφs h).2)
  have hfR : f R = 0 := by simp only [f, spectralRealSchwartzTest_apply, hφR, Complex.ofReal_zero]
  have hφs' : tsupport φ ⊆ Ioo 0 R := fun x hx =>
    ⟨hL.trans_lt (hφs hx).1,(hφs hx).2⟩
  have ht : spectralFirstTest ell R f ∈ spectralHarmonicCoreSubspace ell R L :=
    spectralFirstTest_core ell R L f (fun x hx => by
      have hz : φ x = 0 := image_eq_zero_of_notMem_tsupport
        (fun hm => (not_lt_of_ge hx) (hφs hm).1)
      simp only [f, spectralRealSchwartzTest_apply, hz, Complex.ofReal_zero])
  have hb := spectralFirstChain_flux_balance ell R hR w a u₀ u₁ c ζ B B' f hfR
    (he ⟨_,ht⟩)
  simp only [f, spectralRealSchwartzTest_deriv, spectralRealSchwartzTest_apply,
    Complex.star_def, Complex.conj_ofReal] at hb
  have hreorder : (fun (x : ℝ) => (x : ℂ)^11 * ((φ x : ℂ) *
      (w.density x • spectralHarmonicValue ell R u₀.snd x))) =
      (fun (x : ℝ) => φ x • ((x : ℂ)^11 *
        (w.density x • spectralHarmonicValue ell R u₀.snd x))) := by
    funext x
    simp only [Complex.real_smul]
    ring
  rw [hreorder] at hb
  simp only [← Complex.real_smul] at hb
  rw [spectralCompactTest_integral R (deriv φ) _ (tsupport_deriv_subset.trans hφs'),
    spectralCompactTest_integral R φ _ hφs', spectralCompactTest_integral R φ _ hφs'] at hb
  have hsrc : (∫ x, φ x • spectralSecondSource ell R w (spectralSwapPair ell R u₁) (-c) (-ζ) x) =
      ∫ x, φ x • spectralSecondContinuousSource ell R hR w (spectralSwapPair ell R u₁) (-c) (-ζ) x := by
    apply integral_congr_ae
    have hae := (ae_restrict_iff' measurableSet_Icc).mp (spectralSecondSource_ae ell R hR w (spectralSwapPair ell R u₁) (-c) (-ζ))
    filter_upwards [hae] with x hx
    by_cases hm : x ∈ Icc (0 : ℝ) R
    · rw [hx hm]
    · rw [image_eq_zero_of_notMem_tsupport (fun h => hm (Ioo_subset_Icc_self (hφs' h)))]
      simp only [zero_smul]
  have hforce : (∫ x, φ x • ((x : ℂ)^11 *
      (w.density x • spectralHarmonicValue ell R u₀.snd x))) =
      ∫ x, φ x • ((x : ℂ)^11 *
        (w.density x • spectralHarmonicRepresentative ell R hR u₀.snd x)) := by
    apply integral_congr_ae
    have hae := (ae_restrict_iff' measurableSet_Icc).mp
      (spectralHarmonicRepresentative_ae ell R hR u₀.snd)
    filter_upwards [hae] with x hx
    by_cases hm : x ∈ Icc (0 : ℝ) R
    · rw [hx hm]
    · rw [image_eq_zero_of_notMem_tsupport (fun h => hm (Ioo_subset_Icc_self (hφs' h)))]
      simp only [zero_smul]
  rw [hsrc, hforce] at hb
  have hSc := spectralSecondContinuousSource_continuousOn ell R hR w (spectralSwapPair ell R u₁) (-c) (-ζ) hw
  have hFc : ContinuousOn (fun (x : ℝ) => (x : ℂ)^11 *
      (w.density x • spectralHarmonicRepresentative ell R hR u₀.snd x)) (Ioo 0 R) :=
    (Complex.continuous_ofReal.continuousOn.pow 11).mul
    (hw.smul (spectralHarmonicRepresentative_continuousOn ell R hR u₀.snd))
  have hiS := spectralCompactTest_integrable R φ hφ.continuous hφc hφs' _ hSc
  have hiF := spectralCompactTest_integrable R φ hφ.continuous hφc hφs' _ hFc
  have hsplit : (fun (x : ℝ) => φ x • spectralFirstChainSource ell R hR w u₀ u₁ c ζ x) =
      (fun (x : ℝ) => φ x • spectralSecondContinuousSource ell R hR w (spectralSwapPair ell R u₁) (-c) (-ζ) x) +
      (fun (x : ℝ) => φ x • ((x : ℂ)^11 *
        (w.density x • spectralHarmonicRepresentative ell R hR u₀.snd x))) := by
    funext x
    exact smul_add _ _ _
  rw [hsplit]
  change (∫ x, deriv φ x • spectralSecondFlux ell R w (spectralNegWeight a) (spectralSwapPair ell R u₁) x) =
    -(∫ x, φ x • spectralSecondContinuousSource ell R hR w (spectralSwapPair ell R u₁) (-c) (-ζ) x +
      φ x • ((x : ℂ)^11 * (w.density x • spectralHarmonicRepresentative ell R hR u₀.snd x)))
  rw [integral_add hiS hiF]
  linear_combination hb

theorem spectralFirstChain_classical (ell : ℕ) (L R : ℝ) (hL : 0 ≤ L) (hR : 0 < R)
    (w a : SpectralHarmonicWeight R) (u₀ u₁ : SpectralHarmonicPair ell R) (c ζ : ℂ)
    (B B' : ℂ × ℂ →L[ℂ] ℂ × ℂ)
    (hw : ContinuousOn w.density (Ioo 0 R)) (ha : ContinuousOn a.density (Ioo 0 R))
    (hpos : ∀ x ∈ Ioo 0 R, 0 < w.density x)
    (he : ∀ v : spectralHarmonicCoreSubspace ell R L,
      spectralHarmonicPairComplexForm ell R w u₁ v =
      inner ℂ (spectralLowerOrderOperator ell R hR
        (spectralRadialWeightMultiplier R w) (spectralRadialWeightMultiplier R a) c ζ B
        (spectralHarmonicObservation ell R hR u₁) +
        spectralLowerOrderSlope ell R hR (spectralRadialWeightMultiplier R w) B'
          (spectralHarmonicObservation ell R hR u₀)) v) :
    DifferentiableOn ℝ (spectralHarmonicRepresentative ell R hR u₁.fst) (Ioo L R) ∧
      ContinuousOn (deriv (spectralHarmonicRepresentative ell R hR u₁.fst)) (Ioo L R) ∧
      ∀ x ∈ Ioo L R, HasDerivAt
        (spectralSecondClassicalFlux ell R hR w (spectralNegWeight a) (spectralSwapPair ell R u₁))
        (spectralFirstChainSource ell R hR w u₀ u₁ c ζ x) x := by
  have hs : Ioo L R ⊆ Ioo 0 R := fun x hx => ⟨hL.trans_lt hx.1,hx.2⟩
  exact spectralSecond_forced_classical_annulus ell L R hL hR
    w (spectralNegWeight a) (spectralSwapPair ell R u₁) _
    (hw.mono hs) (ha.neg.mono hs) (fun x hx => hpos x (hs hx))
    ((spectralFirstChainSource_continuousOn ell R hR w u₀ u₁ c ζ hw).mono hs)
    ((spectralSecondFlux_locallyIntegrableOn ell R w (spectralNegWeight a)
      (spectralSwapPair ell R u₁) hw ha.neg).mono_set hs)
    (spectralFirstChain_weak_flux ell L R hL hR w a u₀ u₁ c ζ B B' hw he)

end DefocusingNLS

end OAI
