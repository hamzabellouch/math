import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialMassDerivative
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialTransportIntegration

namespace OAI

/-! The exact radial weighted Green identity for the matched profile. -/

open Set
open scoped ContDiff
namespace DefocusingNLS
open ProfileCertificate

/-- The mass density times the scalar weighted Laplace operator, in its
nonsingular divergence form. -/
noncomputable def radialMassLaplacian (n : ℕ) (z : ProfileMatchingBall)
    (f : ℝ → ℝ) (r : ℝ) : ℝ :=
  -(radialMassDensity n z r*deriv (deriv f) r+radialMassSlope n z r*deriv f r)

theorem radialMassLaplacian_logarithmic (n : ℕ) (z : ProfileMatchingBall)
    (hX : HasRadialExterior (radialShootingNu (n+radialInnerShootingThreshold) z)
      (n+radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius))
    (f : ℝ → ℝ) (r : ℝ) (hr : 0 < r) :
    radialMassLaplacian n z f r=radialMassDensity n z r*
      (-deriv (deriv f) r-(11/r+2*(deriv (radialMatchedProfile n z) r/
        radialMatchedProfile n z r).re)*deriv f r) := by
  unfold radialMassLaplacian
  rw [radialMassSlope_logarithmic n z hX r hr]
  ring

theorem radialMatched_Green_bilinear (n : ℕ) (z : ProfileMatchingBall)
    (hX : HasRadialExterior (radialShootingNu (n+radialInnerShootingThreshold) z)
      (n+radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius))
    (hz : radialMatchingMap n z=0) (R : ℝ) (hR : 0 ≤ R)
    (f g : ℝ → ℝ) (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 1 g) (hgR : g R=0) :
    (∫ r in (0 : ℝ)..R, g r*radialMassLaplacian n z f r)=
      ∫ r in (0 : ℝ)..R, radialMassDensity n z r*deriv g r*deriv f r := by
  have hM := radialMassDensity_continuous n z hX hz
  have hS := radialMassSlope_continuousOn n z hX hz R
  have hfd : ContDiff ℝ 1 (deriv f) := hf.deriv'
  have h1 := hf.continuous_deriv (by norm_num)
  have h2 := hfd.continuous_deriv_one
  have hL : ContinuousOn (radialMassLaplacian n z f) (Icc 0 R) :=
    ((hM.continuousOn.mul h2.continuousOn).add (hS.mul h1.continuousOn)).neg
  have hAi := ((hM.mul hg.continuous_deriv_one).mul h1).intervalIntegrable
    (μ := MeasureTheory.volume) 0 R
  have hBi := (hg.continuous.continuousOn.mul hL).intervalIntegrable_of_Icc
    (μ := MeasureTheory.volume) hR
  have hder (r : ℝ) : HasDerivAt
      (fun t => radialMassDensity n z t*g t*deriv f t)
      (radialMassDensity n z r*deriv g r*deriv f r-g r*radialMassLaplacian n z f r) r := by
    have h := ((radialMassDensity_hasDerivAt n z hX hz r).mul
      (hg.differentiable (by norm_num) r).hasDerivAt).mul
      (hfd.differentiable (by norm_num) r).hasDerivAt
    apply h.congr_deriv
    unfold radialMassLaplacian
    simp only [Pi.mul_apply]
    ring
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun r _ => hder r) (hAi.sub hBi)
  simp only [hgR,mul_zero,zero_mul,radialMassDensity,
    zero_pow (by norm_num : (11 : ℕ)≠0),sub_zero] at he
  change (∫ r in (0 : ℝ)..R,
    (radialMassDensity n z * deriv g * deriv f) r-(g * radialMassLaplacian n z f) r)=0 at he
  rw [intervalIntegral.integral_sub hAi hBi] at he
  exact (sub_eq_zero.mp he).symm

theorem radialMatched_Green_energy (n : ℕ) (z : ProfileMatchingBall)
    (hX : HasRadialExterior (radialShootingNu (n+radialInnerShootingThreshold) z)
      (n+radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius))
    (hz : radialMatchingMap n z=0) (R : ℝ) (hR : 0 ≤ R)
    (f : ℝ → ℝ) (hf : ContDiff ℝ 2 f) (hfR : f R=0) :
    (∫ r in (0 : ℝ)..R, f r*radialMassLaplacian n z f r)=
      ∫ r in (0 : ℝ)..R, radialMassDensity n z r*(deriv f r)^2 := by
  simpa only [pow_two,mul_assoc] using radialMatched_Green_bilinear n z hX hz R hR f f hf
    (hf.of_le (by norm_num)) hfR

end DefocusingNLS

end OAI
