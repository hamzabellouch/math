import OAI.Analysis.KadisonKastler.L2FourierNaturality
import OAI.Analysis.KadisonKastler.FrequencyCovariance

namespace OAI

/-! # Transport of regular operators through a bounded intertwiner -/

namespace KadisonKastler

open MeasureTheory Filter
open scoped FourierTransform

noncomputable section

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

omit [CompleteSpace H] [CompleteSpace K] in
theorem compLp_regularFieldOperator {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (L : H →L[ℂ] K) (A : X → H →L[ℂ] H) (B : X → K →L[ℂ] K)
    (hA : ∀ x, AEStronglyMeasurable (fun t => A t x) μ)
    (hB : ∀ x, AEStronglyMeasurable (fun t => B t x) μ)
    (C D : ℝ) (hC : ∀ᵐ t ∂μ, ‖A t‖ ≤ C) (hD : ∀ᵐ t ∂μ, ‖B t‖ ≤ D)
    (hL : ∀ t x, L (A t x) = B t (L x)) (f : Lp H 2 μ) :
    L.compLp (regularFieldOperator μ A hA C hC f) =
      regularFieldOperator μ B hB D hD (L.compLp f) := by
  apply Lp.ext
  filter_upwards [L.coeFn_compLp (regularFieldOperator μ A hA C hC f),
    regularFieldOperator_represents μ A hA C hC f,
    regularFieldOperator_represents μ B hB D hD (L.compLp f),
    L.coeFn_compLp f] with t hl ha hb hf
  rw [hl, ha, hb, hf, hL]

theorem compLp_regularGauge (L : H →L[ℂ] K)
    (U : Multiplicative ℝ →* unitary (H →L[ℂ] H))
    (V : Multiplicative ℝ →* unitary (K →L[ℂ] K))
    (hU : ∀ x, Continuous (fun t : ℝ => (U (Multiplicative.ofAdd t) : H →L[ℂ] H) x))
    (hV : ∀ x, Continuous (fun t : ℝ => (V (Multiplicative.ofAdd t) : K →L[ℂ] K) x))
    (hL : ∀ t x, L ((U t : H →L[ℂ] H) x) = (V t : K →L[ℂ] K) (L x))
    (f : RegularCoreHilbert H) :
    L.compLp ((regularGauge U hU : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) f) =
      (regularGauge V hV : RegularCoreHilbert K →L[ℂ] RegularCoreHilbert K) (L.compLp f) := by
  apply Lp.ext
  filter_upwards [L.coeFn_compLp ((regularGauge U hU : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) f),
    regularGauge_apply_ae U hU f, regularGauge_apply_ae V hV (L.compLp f),
    L.coeFn_compLp f] with t hl hu hv hf
  rw [hl, hu, hv, hf, hL]

omit [CompleteSpace H] [CompleteSpace K] in
theorem compLp_regularIndicatorProjection (L : H →L[ℂ] K) (s : Set ℝ) (hs : MeasurableSet s)
    (f : RegularCoreHilbert H) :
    L.compLp (regularIndicatorProjection s hs f) = regularIndicatorProjection s hs (L.compLp f) := by
  apply Lp.ext
  filter_upwards [L.coeFn_compLp (regularIndicatorProjection s hs f),
    regularIndicatorProjection_apply_ae s hs f,
    regularIndicatorProjection_apply_ae s hs (L.compLp f), L.coeFn_compLp f] with t hl hp hq hf
  rw [hl, hp, hq]
  by_cases ht : t ∈ s
  · rw [Set.indicator_of_mem ht, Set.indicator_of_mem ht, hf]
  · rw [Set.indicator_of_notMem ht, Set.indicator_of_notMem ht, map_zero]

theorem compLp_fourierInv (L : H →L[ℂ] K) (f : RegularCoreHilbert H) :
    L.compLp ((Lp.fourierTransformₗᵢ ℝ H).symm f) =
      (Lp.fourierTransformₗᵢ ℝ K).symm (L.compLp f) := by
  apply (Lp.fourierTransformₗᵢ ℝ K).injective
  rw [LinearIsometryEquiv.apply_symm_apply]
  have h := fourier_compLp L ((Lp.fourierTransformₗᵢ ℝ H).symm f)
  change (Lp.fourierTransformₗᵢ ℝ K) (L.compLp ((Lp.fourierTransformₗᵢ ℝ H).symm f)) =
    L.compLp ((Lp.fourierTransformₗᵢ ℝ H) ((Lp.fourierTransformₗᵢ ℝ H).symm f)) at h
  simpa only [LinearIsometryEquiv.apply_symm_apply] using h

theorem compLp_regularFrequencyProjection (L : H →L[ℂ] K) (a : ℝ) (f : RegularCoreHilbert H) :
    L.compLp (regularFrequencyProjection a f) = regularFrequencyProjection a (L.compLp f) := by
  change L.compLp ((Lp.fourierTransformₗᵢ ℝ H).symm
    (regularIndicatorProjection (Set.Ioi (a / (2 * Real.pi))) measurableSet_Ioi
      ((Lp.fourierTransformₗᵢ ℝ H) f))) =
    (Lp.fourierTransformₗᵢ ℝ K).symm
      (regularIndicatorProjection (Set.Ioi (a / (2 * Real.pi))) measurableSet_Ioi
        ((Lp.fourierTransformₗᵢ ℝ K) (L.compLp f)))
  rw [compLp_fourierInv, compLp_regularIndicatorProjection]
  exact congrArg (fun g => (Lp.fourierTransformₗᵢ ℝ K).symm
    (regularIndicatorProjection (Set.Ioi (a / (2 * Real.pi))) measurableSet_Ioi g))
    (fourier_compLp L f).symm

end

end KadisonKastler

end OAI
