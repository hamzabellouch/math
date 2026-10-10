import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralTurningPositiveScale
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralLiouvilleResidualContinuity

namespace OAI

/-! The actual complex residual has the same parameter-uniform near-turn bound. -/

open Set MeasureTheory
namespace DefocusingNLS

theorem spectralTurning_complex_scaled_integral (h b eta omega gamma r₀ d M c : ℝ)
    (heta : 0≤eta) (hr₀ : 0<r₀) (hd : 0<d) (hM : 0<M)
    (hac : r₀+M*d≤c) (hc : c≤2*r₀)
    (hz : homogeneousSpectralLocalizationFrequency h b eta omega r₀=0)
    (hscale : spectralLiouvilleSlope eta r₀*d^3=1) :
    (∫ t in (r₀+M*d)..c,
      ‖spectralLiouvilleResidual 1 h b eta omega gamma t‖/
        ‖spectralLiouvilleMomentum 1 h b eta omega gamma t‖)≤
      5/(3*(Real.sqrt (M/8))^3)+3*d/(r₀*Real.sqrt (M/8)) := by
  let a := r₀+M*d
  let F := homogeneousSpectralLocalizationFrequency h b eta omega
  have ha : r₀<a := by dsimp only [a]; nlinarith
  have ha0 : 0<a := hr₀.trans ha
  have ht0 (t : ℝ) (ht : t ∈ Icc a c) : 0<t := ha0.trans_le ht.1
  have hF0 (t : ℝ) (ht : t ∈ Icc a c) : 0<F t := by
    have hh := homogeneousSpectralLocalizationFrequency_strictMono h b eta omega heta
      hr₀ (ht0 t ht) (ha.trans_le ht.1)
    simpa only [hz] using hh
  have hFc : ContinuousOn F (Icc a c) := fun t ht =>
    (homogeneousSpectralLocalizationFrequency_hasDerivAt h b eta omega t
      (ht0 t ht)).continuousAt.continuousWithinAt
  have hp : ContinuousOn (fun t => Real.sqrt (F t)) (Icc a c) :=
    Real.continuous_sqrt.comp_continuousOn hFc
  have hpn (t : ℝ) (ht : t ∈ Icc a c) : Real.sqrt (F t)≠0 :=
    (Real.sqrt_pos.2 (hF0 t ht)).ne'
  have hg : ContinuousOn (spectralLiouvilleSlope eta) (Icc a c) := fun t ht =>
    (spectralLiouvilleSlope_hasDerivAt eta t (ht0 t ht)).continuousAt.continuousWithinAt
  have he : ContinuousOn (spectralLiouvilleSecond eta) (Icc a c) := by
    apply continuousOn_const.sub
    apply continuousOn_const.div (continuousOn_id.pow 4)
    exact fun t ht => pow_ne_zero _ (ht0 t ht).ne'
  have hreal : ContinuousOn (fun t => (5/16 : ℝ)*(spectralLiouvilleSlope eta t)^2/
      (Real.sqrt (F t))^5+|spectralLiouvilleSecond eta t|/(4*(Real.sqrt (F t))^3))
      (Icc a c) := ((continuousOn_const.mul (hg.pow 2)).div (hp.pow 5)
    (fun t ht => pow_ne_zero _ (hpn t ht))).add
    (he.abs.div (continuousOn_const.mul (hp.pow 3))
      (fun t ht => mul_ne_zero (by norm_num) (pow_ne_zero _ (hpn t ht))))
  have hcomplex := (spectralLiouvilleResidual_continuousOn 1 h b eta omega gamma a c
    (by norm_num) ha0 (fun t ht => by simpa only [one_mul] using hF0 t ht)).2
  have hle := intervalIntegral.integral_mono_on (μ := volume) hac
    (hcomplex.intervalIntegrable_of_Icc hac) (hreal.intervalIntegrable_of_Icc hac)
    (fun t ht => by
      have hh := spectralLiouville_weighted_residual_le 1 h b eta omega gamma t
        (by norm_num) (hF0 t ht).ne'
      have hFt : 0<homogeneousSpectralLocalizationFrequency h b eta omega t := hF0 t ht
      simpa only [abs_of_pos hFt] using hh)
  exact hle.trans (spectralTurning_positive_scaled_integral h b eta omega r₀ d M c
    heta hr₀ hd hM hac hc hz hscale)

end DefocusingNLS

end OAI
