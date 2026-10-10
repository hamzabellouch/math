import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralLiouvilleEndpoint
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralTurningOuterDerivative
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralTurningOuterPhase
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralTurningOuterNegative

namespace OAI

/-! Uniform actual-solution transfer on the whole forbidden outer interval. -/

open Set MeasureTheory
namespace DefocusingNLS

theorem spectralTurning_negative_endpoint_transfer
    (h b eta omega gamma r₀ d M R : ℝ)
    (heta : 0≤eta) (hr₀ : 0<r₀) (hd : 0<d) (hM : 32≤M)
    (hR : 0<R) (hlarge : 16≤r₀*R) (hRhalf : R≤r₀/2) (hMd : M*d≤r₀/2)
    (hz : homogeneousSpectralLocalizationFrequency h b eta omega r₀=0)
    (hscale : spectralLiouvilleSlope eta r₀*d^3=1)
    (q : ℝ → ℂ × ℂ) (hq : ContinuousOn q (Icc R (r₀-M*d)))
    (hODE : ∀ t ∈ Ioo R (r₀-M*d), HasDerivAt q
      (spectralScalarField ((homogeneousSpectralLocalizationFrequency h b eta omega t : ℂ)+
        Complex.I*(gamma : ℂ)) (q t)) t) :
    spectralShellNorm (Real.sqrt ‖spectralLiouvilleMomentum (-1) h b eta omega gamma (r₀-M*d)‖)
      (q (r₀-M*d))≤
      (25/4 : ℝ)*spectralShellNorm (Real.sqrt ‖spectralLiouvilleMomentum (-1) h b eta omega gamma R‖) (q R)*
      Real.exp ((∫ t in R..(r₀-M*d), Real.sqrt (-homogeneousSpectralLocalizationFrequency h b eta omega t))+
        |gamma| * 260+(25/4)*(5/(3*(Real.sqrt (M/8))^3)+3*d/(r₀*Real.sqrt (M/8))+64/(r₀*R))) := by
  let c := r₀-M*d
  have hMp : 0<M := by linarith
  have hc : c<r₀ := by dsimp only [c]; nlinarith
  have hRc : R≤c := by dsimp only [c]; linarith
  have hF (t : ℝ) (ht : t ∈ Icc R c) :
      0<(-1)*homogeneousSpectralLocalizationFrequency h b eta omega t := by
    have hf := homogeneousSpectralLocalizationFrequency_strictMono h b eta omega heta
      (hR.trans_le ht.1) hr₀ (ht.2.trans_lt hc)
    rw [hz] at hf
    linarith
  have hphase (t : ℝ) (_ : t ∈ Ioo R c) :
      0≤((1 : ℂ)*spectralLiouvilleMomentum (-1) h b eta omega gamma t).re := by
    simpa only [one_mul,spectralLiouvilleMomentum] using
      spectralComplexSqrt_re_nonneg (spectralWKBSquaredMomentum (-1)
        (homogeneousSpectralLocalizationFrequency h b eta omega t) gamma)
  have ht := spectralLiouville_endpoint_bound (-1) h b eta omega gamma R c 260
    (5/(3*(Real.sqrt (M/8))^3)+3*d/(r₀*Real.sqrt (M/8))+64/(r₀*R))
    (by norm_num) hR hRc 1 (by norm_num) (by norm_num) hF
    (fun t ht => spectralTurning_negative_derivative_small (-1) h b eta omega gamma r₀ d M R t
      (by norm_num) heta hr₀ hd hM hR hlarge ht.1 ht.2 hz hscale) hphase
    (by
      simpa only [neg_one_mul] using
        spectralTurning_negative_outer_phase h b eta omega r₀ d M R
          heta hr₀ hd hMp hR hRhalf hMd hz)
    (spectralTurning_outer_negative_error h b eta omega gamma r₀ d M R
      heta hr₀ hd hMp hR hRhalf hMd hz hscale) q hq hODE
  simpa only [Complex.one_re,one_mul,neg_one_mul] using ht

end DefocusingNLS

end OAI
