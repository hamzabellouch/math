import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialAngularScalarEstimates

namespace OAI

/-! The angular barrier in the actual weighted radial energy on a fixed ball. -/

open Set
open scoped ContDiff
namespace DefocusingNLS
open ProfileCertificate

theorem homogeneousSpectralLocalization_angular_barrier
    (n : ℕ) (z : ProfileMatchingBall)
    (hX : HasRadialExterior (radialShootingNu (n + radialInnerShootingThreshold) z)
      (n + radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius))
    (hz : radialMatchingMap n z = 0) (η R : ℝ) (hη : 0 ≤ η) (hR : 0 < R)
    (f : ℝ → ℝ) (hf : Continuous f) :
    η / R^2 * (∫ r in (0 : ℝ)..R, radialMassDensity n z r * (f r)^2) ≤
      η * radialAngularForm n z R f f := by
  have hMi := ((radialMassDensity_continuous n z hX hz).mul (hf.pow 2)).intervalIntegrable
    (μ := MeasureTheory.volume) 0 R
  have hKi := ((radialAngularDensity_continuous n z hX hz).mul (hf.pow 2)).intervalIntegrable
    (μ := MeasureTheory.volume) 0 R
  have he : ∀ r ∈ Icc 0 R,
      η / R^2 * (radialMassDensity n z r * (f r)^2) ≤
        η * (radialAngularDensity n z r * (f r)^2) := by
    intro r hr
    have hr0 := hr.1
    have hp : 0 ≤ radialAngularDensity n z r * (f r)^2 := by
      dsimp only [radialAngularDensity]
      positivity
    have hm : radialMassDensity n z r = r^2 * radialAngularDensity n z r := by
      dsimp only [radialMassDensity, radialAngularDensity]
      ring
    rw [hm]
    have hrr : r^2 ≤ R^2 := (sq_le_sq₀ hr.1 hR.le).mpr hr.2
    have hquot : η / R^2 * r^2 ≤ η := by
      calc
        _ = (η * r^2) / R^2 := by ring
        _ ≤ η := (div_le_iff₀ (sq_pos_of_pos hR)).mpr
          (mul_le_mul_of_nonneg_left hrr hη)
    calc
      _ = (η / R^2 * r^2) * (radialAngularDensity n z r * (f r)^2) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hquot hp
  have hi := intervalIntegral.integral_mono_on hR.le
    (hMi.const_mul (η / R^2)) (hKi.const_mul η) he
  simpa only [intervalIntegral.integral_const_mul, radialAngularForm_diag,
    Pi.mul_apply, Pi.pow_apply] using hi

theorem homogeneousSpectralLocalization_energy_barrier
    (n : ℕ) (z : ProfileMatchingBall)
    (hX : HasRadialExterior (radialShootingNu (n + radialInnerShootingThreshold) z)
      (n + radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius))
    (hz : radialMatchingMap n z = 0) (η R : ℝ) (hη : 0 ≤ η) (hR : 0 < R)
    (q f : ℝ → ℝ) (hf : Continuous f) (hq : ∀ r ∈ Icc 0 R, 0 ≤ q r) :
    η / R^2 * (∫ r in (0 : ℝ)..R, radialMassDensity n z r * (f r)^2) ≤
      radialAngularScalarForm n z η R q f f := by
  have hb := homogeneousSpectralLocalization_angular_barrier n z hX hz η R hη hR f hf
  have he := radialScalarForm_nonneg n z R hR.le q f hq
  unfold radialAngularScalarForm
  linarith

end DefocusingNLS

end OAI
