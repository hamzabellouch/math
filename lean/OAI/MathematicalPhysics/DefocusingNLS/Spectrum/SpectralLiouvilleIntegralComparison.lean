import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralLiouvilleResidualContinuity
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralWKBResidualIntegral

namespace OAI

/-! Integral comparison for the actual complex residual on a fixed-sign interval. -/

open Set MeasureTheory
namespace DefocusingNLS

theorem spectralLiouville_residual_integral_le
    (sign h b eta omega gamma a c : ℝ) (hs : sign^2=1) (ha : 0<a) (hac : a≤c)
    (hF : ∀ t ∈ Icc a c, 0<sign*homogeneousSpectralLocalizationFrequency h b eta omega t) :
    (∫ t in a..c, ‖spectralLiouvilleResidual sign h b eta omega gamma t‖/
      ‖spectralLiouvilleMomentum sign h b eta omega gamma t‖)≤
    ∫ t in a..c, (5/16 : ℝ)*(spectralLiouvilleSlope eta t)^2/
      (Real.sqrt |homogeneousSpectralLocalizationFrequency h b eta omega t|)^5+
      |spectralLiouvilleSecond eta t|/
        (4*(Real.sqrt |homogeneousSpectralLocalizationFrequency h b eta omega t|)^3) := by
  let F := homogeneousSpectralLocalizationFrequency h b eta omega
  have ht0 (t : ℝ) (ht : t ∈ Icc a c) : 0<t := ha.trans_le ht.1
  have hFn (t : ℝ) (ht : t ∈ Icc a c) : F t≠0 := by
    intro he
    have hh := hF t ht
    change 0<sign*F t at hh
    rw [he,mul_zero] at hh
    exact lt_irrefl _ hh
  have hFc : ContinuousOn F (Icc a c) := fun t ht =>
    (homogeneousSpectralLocalizationFrequency_hasDerivAt h b eta omega t
      (ht0 t ht)).continuousAt.continuousWithinAt
  have hp : ContinuousOn (fun t => Real.sqrt |F t|) (Icc a c) :=
    Real.continuous_sqrt.comp_continuousOn hFc.abs
  have hpn (t : ℝ) (ht : t ∈ Icc a c) : Real.sqrt |F t|≠0 :=
    (Real.sqrt_pos.2 (abs_pos.2 (hFn t ht))).ne'
  have hg : ContinuousOn (spectralLiouvilleSlope eta) (Icc a c) := fun t ht =>
    (spectralLiouvilleSlope_hasDerivAt eta t (ht0 t ht)).continuousAt.continuousWithinAt
  have he : ContinuousOn (spectralLiouvilleSecond eta) (Icc a c) := by
    apply continuousOn_const.sub
    apply continuousOn_const.div (continuousOn_id.pow 4)
    exact fun t ht => pow_ne_zero _ (ht0 t ht).ne'
  have hreal : ContinuousOn (fun t => (5/16 : ℝ)*(spectralLiouvilleSlope eta t)^2/
      (Real.sqrt |F t|)^5+|spectralLiouvilleSecond eta t|/(4*(Real.sqrt |F t|)^3))
      (Icc a c) := ((continuousOn_const.mul (hg.pow 2)).div (hp.pow 5)
      (fun t ht => pow_ne_zero _ (hpn t ht))).add
      (he.abs.div (continuousOn_const.mul (hp.pow 3))
        (fun t ht => mul_ne_zero (by norm_num) (pow_ne_zero _ (hpn t ht))))
  have hcomplex := (spectralLiouvilleResidual_continuousOn sign h b eta omega gamma a c hs ha hF).2
  exact intervalIntegral.integral_mono_on hac
    (hcomplex.intervalIntegrable_of_Icc hac) (hreal.intervalIntegrable_of_Icc hac)
    (fun t ht => spectralLiouville_weighted_residual_le sign h b eta omega gamma t hs (hFn t ht))

end DefocusingNLS

end OAI
