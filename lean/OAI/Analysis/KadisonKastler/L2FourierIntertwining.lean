import OAI.Analysis.KadisonKastler.L2GaugeStarTransport

namespace OAI

/-! # Transporting Fourier conjugacy through a bounded intertwiner -/

namespace KadisonKastler

open MeasureTheory
open scoped FourierTransform

noncomputable section

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

theorem compLp_regularGaugeFrequency (L : H →L[ℂ] K)
    (U : Multiplicative ℝ →* unitary (H →L[ℂ] H))
    (V : Multiplicative ℝ →* unitary (K →L[ℂ] K))
    (hU : ∀ x, Continuous (fun t : ℝ => (U (Multiplicative.ofAdd t) : H →L[ℂ] H) x))
    (hV : ∀ x, Continuous (fun t : ℝ => (V (Multiplicative.ofAdd t) : K →L[ℂ] K) x))
    (hL : ∀ t x, L ((U t : H →L[ℂ] H) x) = (V t : K →L[ℂ] K) (L x))
    (a : ℝ) (F : RegularCoreHilbert H) :
    L.compLp ((star (regularGauge U hU) : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)
      (regularFrequencyProjection a ((regularGauge U hU :
        RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) F))) =
    (star (regularGauge V hV) : RegularCoreHilbert K →L[ℂ] RegularCoreHilbert K)
      (regularFrequencyProjection a ((regularGauge V hV :
        RegularCoreHilbert K →L[ℂ] RegularCoreHilbert K) (L.compLp F))) := by
  rw [compLp_regularGauge_star L U V hU hV hL, compLp_regularFrequencyProjection,
    compLp_regularGauge L U V hU hV hL]

theorem fourier_intertwines_of_transport (L : H →L[ℂ] K)
    (A B : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)
    (C D : RegularCoreHilbert K →L[ℂ] RegularCoreHilbert K)
    (hA : ∀ F, L.compLp (A F) = C (L.compLp F))
    (hB : ∀ F, L.compLp (B F) = D (L.compLp F))
    (hAB : ∀ F, (𝓕 (A F) : RegularCoreHilbert H) = B (𝓕 F)) (F : RegularCoreHilbert H) :
    (𝓕 (C (L.compLp F)) : RegularCoreHilbert K) = D (𝓕 (L.compLp F)) := by
  calc
    _ = 𝓕 (L.compLp (A F)) := congrArg (fun W : RegularCoreHilbert K => 𝓕 W) (hA F).symm
    _ = L.compLp (𝓕 (A F)) := fourier_compLp L (A F)
    _ = L.compLp (B (𝓕 F)) := congrArg L.compLp (hAB F)
    _ = D (L.compLp (𝓕 F)) := hB (𝓕 F)
    _ = _ := congrArg D (fourier_compLp L F).symm

end

end KadisonKastler

end OAI
