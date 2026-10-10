import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousSpectralLocalizationGauge
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralSubunitCoefficients
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialUniformExteriorPressure

namespace OAI

/-! The Liouville gauge preserves the uniform inverse-square coupling bound. -/

open Set Filter
namespace DefocusingNLS
open ProfileCertificate

theorem homogeneousSpectralLocalization_phase_norm (h r : ℝ) (hr : 0 < r) :
    ‖homogeneousSpectralLocalizationFactor h r /
      homogeneousSpectralLocalizationFactor (-h) r‖ = 1 := by
  rw [norm_div, homogeneousSpectralLocalizationFactor_norm h r hr,
    homogeneousSpectralLocalizationFactor_norm (-h) r hr,
    div_self (Real.rpow_pos_of_pos hr _).ne']

theorem homogeneousSpectralLocalization_coupling_bound
    (h r : ℝ) (hr : 0 < r) (D C u v : ℂ) :
    ‖D * u + C * (homogeneousSpectralLocalizationFactor h r /
      homogeneousSpectralLocalizationFactor (-h) r) * v‖ ≤
      (‖D‖ + ‖C‖) * max ‖u‖ ‖v‖ := by
  calc
    _ ≤ ‖D * u‖ + ‖C * (homogeneousSpectralLocalizationFactor h r /
        homogeneousSpectralLocalizationFactor (-h) r) * v‖ := norm_add_le _ _
    _ = ‖D‖ * ‖u‖ + ‖C‖ * ‖v‖ := by
      rw [norm_mul, norm_mul, norm_mul, homogeneousSpectralLocalization_phase_norm h r hr,
        mul_one]
    _ ≤ ‖D‖ * max ‖u‖ ‖v‖ + ‖C‖ * max ‖u‖ ‖v‖ :=
      add_le_add (mul_le_mul_of_nonneg_left (le_max_left _ _) (norm_nonneg _))
        (mul_le_mul_of_nonneg_left (le_max_right _ _) (norm_nonneg _))
    _ = _ := by ring

theorem homogeneousSpectralLocalization_uniform_potential (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ z : ProfileMatchingBall, ∀ r : ℝ, innerBoundaryRadius < r →
      r^2 * (‖spectralDiagonalCoefficient (n + radialInnerShootingThreshold)
        (radialMatchedProfile n z r)‖ +
        ‖spectralCrossCoefficient (n + radialInnerShootingThreshold)
          (radialMatchedProfile n z r)‖) < ε := by
  filter_upwards [radialMatched_exterior_pressure_small (ε / 2) (by positivity)] with n hn z r hr
  let m := n + radialInnerShootingThreshold
  let a := radialShootingA n
  let P := ‖radialMatchedProfile n z r‖^(2*m)
  have ha : 0 < a := (radialShootingA_bounds n (profileMatchingParameter z)).1
  have ha1 : a < 1 := (radialShootingA_bounds n (profileMatchingParameter z)).2
  have hma : 2 * a * (m : ℝ) = 1 := radialShootingA_power n (profileMatchingParameter z)
  have hm : 1 ≤ m := radialShootingInner_power_pos n (profileMatchingParameter z)
  have hcoef : (2 * (m : ℝ) + 1) * a ≤ 2 := by nlinarith
  have hnonneg : 0 ≤ r^2 * (P / a) := by positivity
  have he : r^2 * ((2 * (m : ℝ) + 1) * P) =
      ((2 * (m : ℝ) + 1) * a) * (r^2 * (P / a)) := by
    field_simp [ha.ne']
  rw [spectralCoefficient_norm_sum _ hm]
  change r^2 * ((2 * (m : ℝ) + 1) * P) < ε
  rw [he]
  have hb : r^2 * (P / a) < ε / 2 := hn z r hr
  exact (mul_le_mul_of_nonneg_right hcoef hnonneg).trans_lt (by linarith)

end DefocusingNLS

end OAI
