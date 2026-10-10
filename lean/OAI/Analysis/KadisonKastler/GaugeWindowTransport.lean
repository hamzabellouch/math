import OAI.Analysis.KadisonKastler.CoreTraceScalarGauge
import OAI.Analysis.KadisonKastler.L2GaugeStarTransport
import OAI.Analysis.KadisonKastler.L2FourierNaturality

namespace OAI

/-! # Transport of a frequency-window identity along a group intertwiner -/

namespace KadisonKastler

open MeasureTheory
open scoped FourierTransform

noncomputable section

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

theorem compLp_regularFrequencyWindow (L : H →L[ℂ] K) (a b : ℝ)
    (f : RegularCoreHilbert H) :
    L.compLp (regularFrequencyWindow a b f) =
      regularFrequencyWindow a b (L.compLp f) := by
  apply (Lp.fourierTransformₗᵢ ℝ K).injective
  change (𝓕 (L.compLp (regularFrequencyWindow a b f)) : RegularCoreHilbert K) =
    𝓕 (regularFrequencyWindow a b (L.compLp f))
  rw [fourier_compLp, fourier_frequencyWindow, fourier_frequencyWindow,
    compLp_regularIndicatorProjection, fourier_compLp]

theorem regularGauge_window_balance_transport (L : H →L[ℂ] K)
    (U : Multiplicative ℝ →* unitary (H →L[ℂ] H))
    (V : Multiplicative ℝ →* unitary (K →L[ℂ] K))
    (hU : ∀ x, Continuous (fun t : ℝ => (U (Multiplicative.ofAdd t) : H →L[ℂ] H) x))
    (hV : ∀ x, Continuous (fun t : ℝ => (V (Multiplicative.ofAdd t) : K →L[ℂ] K) x))
    (hL : ∀ t x, L ((U t : H →L[ℂ] H) x) = (V t : K →L[ℂ] K) (L x))
    (f : Lp ℂ 2 (volume : Measure ℝ)) (v w : H)
    (h : regularFrequencyWindow 0 1
      ((star (regularGauge U hU) : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)
        (scalarLpTensor volume f v)) =
      (star (regularGauge U hU) : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)
        (regularFrequencyWindow 0 1
          ((regularGauge U hU : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)
            (scalarLpTensor volume f w)))) :
    regularFrequencyWindow 0 1
      ((star (regularGauge V hV) : RegularCoreHilbert K →L[ℂ] RegularCoreHilbert K)
        (scalarLpTensor volume f (L v))) =
      (star (regularGauge V hV) : RegularCoreHilbert K →L[ℂ] RegularCoreHilbert K)
        (regularFrequencyWindow 0 1
          ((regularGauge V hV : RegularCoreHilbert K →L[ℂ] RegularCoreHilbert K)
            (scalarLpTensor volume f (L w)))) := by
  have he := congrArg L.compLp h
  rw [compLp_regularFrequencyWindow L,
    compLp_regularGauge_star L U V hU hV hL,
    compLp_scalarLpTensor volume L,
    compLp_regularGauge_star L U V hU hV hL,
    compLp_regularFrequencyWindow L,
    compLp_regularGauge L U V hU hV hL,
    compLp_scalarLpTensor volume L] at he
  exact he

end

end KadisonKastler

end OAI
