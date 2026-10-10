import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralTurningNegativeIntegral
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralLiouvilleIntegralComparison

namespace OAI

/-! Transfer the forbidden-side near-turning estimate to the complex momentum. -/

open Set MeasureTheory
namespace DefocusingNLS

theorem spectralTurning_complex_negative_integral (h b eta omega gamma r₀ d M a : ℝ)
    (heta : 0≤eta) (hr₀ : 0<r₀) (hd : 0<d) (hM : 0<M)
    (ha : r₀/2≤a) (hac : a≤r₀-M*d)
    (hz : homogeneousSpectralLocalizationFrequency h b eta omega r₀=0)
    (hscale : spectralLiouvilleSlope eta r₀*d^3=1) :
    (∫ t in a..(r₀-M*d),
      ‖spectralLiouvilleResidual (-1) h b eta omega gamma t‖/
        ‖spectralLiouvilleMomentum (-1) h b eta omega gamma t‖)≤
      5/(3*(Real.sqrt (M/8))^3)+3*d/(r₀*Real.sqrt (M/8)) := by
  let c := r₀-M*d
  have hc : c<r₀ := by dsimp only [c]; nlinarith
  have ha0 : 0<a := by linarith
  have hF (t : ℝ) (ht : t ∈ Icc a c) :
      homogeneousSpectralLocalizationFrequency h b eta omega t<0 := by
    have hh := homogeneousSpectralLocalizationFrequency_strictMono h b eta omega heta
      (ha0.trans_le ht.1) hr₀ (ht.2.trans_lt hc)
    simpa only [hz] using hh
  have hb := spectralLiouville_residual_integral_le (-1) h b eta omega gamma a c
    (by norm_num) ha0 hac (fun t ht => by simpa only [neg_one_mul] using neg_pos.2 (hF t ht))
  have he : (∫ t in a..c, (5/16 : ℝ)*(spectralLiouvilleSlope eta t)^2/
      (Real.sqrt |homogeneousSpectralLocalizationFrequency h b eta omega t|)^5+
      |spectralLiouvilleSecond eta t|/
        (4*(Real.sqrt |homogeneousSpectralLocalizationFrequency h b eta omega t|)^3))=
      ∫ t in a..c, (5/16 : ℝ)*(spectralLiouvilleSlope eta t)^2/
      (Real.sqrt (-homogeneousSpectralLocalizationFrequency h b eta omega t))^5+
      |spectralLiouvilleSecond eta t|/
        (4*(Real.sqrt (-homogeneousSpectralLocalizationFrequency h b eta omega t))^3) := by
    apply intervalIntegral.integral_congr
    intro t ht
    have htc : t ∈ Icc a c := by simpa only [uIcc_of_le (show a≤c from hac)] using ht
    dsimp only
    rw [abs_of_neg (hF t htc)]
  rw [he] at hb
  exact hb.trans (spectralTurning_negative_scaled_integral h b eta omega r₀ d M a
    heta hr₀ hd hM ha hac hz hscale)

end DefocusingNLS

end OAI
