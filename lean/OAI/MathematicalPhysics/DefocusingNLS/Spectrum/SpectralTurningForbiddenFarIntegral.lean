import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralTurningForbiddenGeometry
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralWKBFarBound
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralLiouvilleResidualContinuity
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralCouplingEstimate

namespace OAI

/-! The far forbidden residual is small uniformly down to a fixed positive radius. -/

open Set MeasureTheory
namespace DefocusingNLS

theorem spectralTurning_forbidden_far_residual (h b eta omega gamma r₀ r : ℝ)
    (heta : 0≤eta) (hr₀ : 0<r₀) (hr : 0<r) (hrr : r≤r₀/2)
    (hz : homogeneousSpectralLocalizationFrequency h b eta omega r₀=0) :
    ‖spectralLiouvilleResidual (-1) h b eta omega gamma r‖/
      ‖spectralLiouvilleMomentum (-1) h b eta omega gamma r‖≤64/(r₀*r^2) := by
  let F := homogeneousSpectralLocalizationFrequency h b eta omega r
  let p := Real.sqrt (-F)
  obtain ⟨hFlo,hFg⟩ := spectralTurning_forbidden_far h b eta omega r₀ r heta hr₀ hr hrr hz
  have hF : F<0 := by
    have hh : 0<r₀^2/32 := by positivity
    change r₀^2/32≤-F at hFlo
    linarith
  have hp : 0<p := Real.sqrt_pos.2 (neg_pos.2 hF)
  have hpsq : p^2=-F := Real.sq_sqrt (neg_pos.2 hF).le
  have hpr : r₀/8≤p := by nlinarith
  have hg : 0≤ spectralLiouvilleSlope eta r := by dsimp only [spectralLiouvilleSlope]; positivity
  have hgp : spectralLiouvilleSlope eta r≤4*p^2/r := by simpa only [hpsq] using hFg
  have hbound := spectralLiouville_weighted_residual_le (-1) h b eta omega gamma r
    (by norm_num) hF.ne
  have hFt : homogeneousSpectralLocalizationFrequency h b eta omega r<0 := hF
  rw [abs_of_neg hFt] at hbound
  calc
    _ ≤ (5/16 : ℝ)*(spectralLiouvilleSlope eta r)^2/p^5+
        |spectralLiouvilleSecond eta r|/(4*p^3) := hbound
    _ ≤ 8/(r^2*p) := spectralWKB_radial_bound r p (spectralLiouvilleSlope eta r)
      (spectralLiouvilleSecond eta r) hr hp hg hgp
      (spectralLiouvilleSecond_relative eta r heta hr)
    _ ≤ 8/(r^2*(r₀/8)) := by gcongr
    _ = 64/(r₀*r^2) := by field_simp; ring

theorem spectralTurning_forbidden_far_integral (h b eta omega gamma r₀ a c : ℝ)
    (heta : 0≤eta) (hr₀ : 0<r₀) (ha : 0<a) (hac : a≤c) (hc : c≤r₀/2)
    (hz : homogeneousSpectralLocalizationFrequency h b eta omega r₀=0) :
    (∫ t in a..c, ‖spectralLiouvilleResidual (-1) h b eta omega gamma t‖/
      ‖spectralLiouvilleMomentum (-1) h b eta omega gamma t‖)≤64/(r₀*a) := by
  have hF (t : ℝ) (ht : t ∈ Icc a c) :
      0<(-1)*homogeneousSpectralLocalizationFrequency h b eta omega t := by
    have hb := (spectralTurning_forbidden_far h b eta omega r₀ t heta hr₀
      (ha.trans_le ht.1) (ht.2.trans hc) hz).1
    have hh : 0<r₀^2/32 := by positivity
    linarith
  have hcont := (spectralLiouvilleResidual_continuousOn (-1) h b eta omega gamma a c
    (by norm_num) ha hF).2
  have hpow : ContinuousOn (fun t : ℝ => (t^2)⁻¹) (Icc a c) :=
    (continuousOn_id.pow 2).inv₀ (fun t ht => pow_ne_zero _ (ha.trans_le ht.1).ne')
  have hint : (∫ t in a..c, ‖spectralLiouvilleResidual (-1) h b eta omega gamma t‖/
      ‖spectralLiouvilleMomentum (-1) h b eta omega gamma t‖)≤
      ∫ t in a..c, (64/r₀)*(t^2)⁻¹ := by
    apply intervalIntegral.integral_mono_on hac (hcont.intervalIntegrable_of_Icc hac)
      ((continuousOn_const.mul hpow).intervalIntegrable_of_Icc hac)
    intro t ht
    have hb := spectralTurning_forbidden_far_residual h b eta omega gamma r₀ t heta hr₀
      (ha.trans_le ht.1) (ht.2.trans hc) hz
    convert hb using 1
    change (64/r₀)*(t^2)⁻¹=64/(r₀*t^2)
    ring
  rw [intervalIntegral.integral_const_mul] at hint
  calc
    _ ≤ (64/r₀)*(∫ t in a..c, (t^2)⁻¹) := hint
    _ ≤ (64/r₀)*a⁻¹ := mul_le_mul_of_nonneg_left
      (spectral_inverse_square_integral_le a c ha hac) (by positivity)
    _ = _ := by ring

end DefocusingNLS

end OAI
