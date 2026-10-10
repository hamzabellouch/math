import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralTurningFarGeometry
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralWKBFarBound
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralInverseCubeIntegral
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralLiouvilleResidualContinuity

namespace OAI

/-! The actual complex WKB residual is integrable past twice the turning radius. -/

open Set MeasureTheory
namespace DefocusingNLS

theorem spectralTurning_far_residual (h b eta omega gamma r₀ r : ℝ)
    (heta : 0≤eta) (hr₀ : 0<r₀) (hr : 2*r₀≤r)
    (hz : homogeneousSpectralLocalizationFrequency h b eta omega r₀=0) :
    ‖spectralLiouvilleResidual 1 h b eta omega gamma r‖/
      ‖spectralLiouvilleMomentum 1 h b eta omega gamma r‖≤64/r^3 := by
  let F := homogeneousSpectralLocalizationFrequency h b eta omega r
  let p := Real.sqrt F
  have hrp : 0<r := by linarith
  obtain ⟨hFlo,hFg⟩ := spectralTurning_far_geometry h b eta omega r₀ r heta hr₀ hr hz
  have hF : 0<F := lt_of_lt_of_le (by positivity : 0<r^2/32) hFlo
  have hp : 0<p := Real.sqrt_pos.2 hF
  have hpsq : p^2=F := Real.sq_sqrt hF.le
  have hpr : r/8≤p := by nlinarith
  have hg : 0≤ spectralLiouvilleSlope eta r := by dsimp only [spectralLiouvilleSlope]; positivity
  have hgp : spectralLiouvilleSlope eta r≤4*p^2/r := by simpa only [hpsq] using hFg
  have hbound := spectralLiouville_weighted_residual_le 1 h b eta omega gamma r
    (by norm_num) hF.ne'
  have hFt : 0<homogeneousSpectralLocalizationFrequency h b eta omega r := hF
  rw [abs_of_pos hFt] at hbound
  exact hbound.trans (spectralWKB_far_bound r p (spectralLiouvilleSlope eta r)
    (spectralLiouvilleSecond eta r) hrp hp hpr hg hgp
    (spectralLiouvilleSecond_relative eta r heta hrp))

theorem spectralTurning_far_integral (h b eta omega gamma r₀ a c : ℝ)
    (heta : 0≤eta) (hr₀ : 0<r₀) (ha : 2*r₀≤a) (hac : a≤c)
    (hz : homogeneousSpectralLocalizationFrequency h b eta omega r₀=0) :
    (∫ t in a..c, ‖spectralLiouvilleResidual 1 h b eta omega gamma t‖/
      ‖spectralLiouvilleMomentum 1 h b eta omega gamma t‖)≤32/a^2 := by
  have ha0 : 0<a := by linarith
  have hF (t : ℝ) (ht : t ∈ Icc a c) :
      0<1*homogeneousSpectralLocalizationFrequency h b eta omega t := by
    have hr : 2*r₀≤t := ha.trans ht.1
    have hFlo := (spectralTurning_far_geometry h b eta omega r₀ t heta hr₀ hr hz).1
    have ht0 : 0<t := ha0.trans_le ht.1
    have hh : 0<t^2/32 := by positivity
    simpa only [one_mul] using hh.trans_le hFlo
  exact spectral_inverse_cube_bound a c ha0 hac _
    (spectralLiouvilleResidual_continuousOn 1 h b eta omega gamma a c
      (by norm_num) ha0 hF).2
    (fun t ht => spectralTurning_far_residual h b eta omega gamma r₀ t heta hr₀
      (ha.trans ht.1) hz)

end DefocusingNLS

end OAI
