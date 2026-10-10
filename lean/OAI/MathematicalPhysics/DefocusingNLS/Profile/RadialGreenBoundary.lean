import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialVelocityCalculus

namespace OAI

/-! Weighted Green integration retaining the outer boundary term. -/

open Set
open scoped ContDiff
namespace DefocusingNLS
open ProfileCertificate

theorem radialMatched_Green_boundary (n : ℕ) (z : ProfileMatchingBall)
    (hX : HasRadialExterior (radialShootingNu (n+radialInnerShootingThreshold) z)
      (n+radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius))
    (hz : radialMatchingMap n z=0) (R : ℝ) (hR : 0 ≤ R)
    (f g : ℝ → ℝ) (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 1 g) :
    (∫ r in (0 : ℝ)..R, g r*radialMassLaplacian n z f r)=
      (∫ r in (0 : ℝ)..R, radialMassDensity n z r*deriv g r*deriv f r)-
        radialMassDensity n z R*g R*deriv f R := by
  have hM := radialMassDensity_continuous n z hX hz
  have hS := radialMassSlope_continuousOn n z hX hz R
  have hfd : ContDiff ℝ 1 (deriv f) := hf.deriv'
  have h1 := hf.continuous_deriv (by norm_num)
  have h2 := hfd.continuous_deriv_one
  have hL : ContinuousOn (radialMassLaplacian n z f) (Icc 0 R) :=
    ((hM.continuousOn.mul h2.continuousOn).add (hS.mul h1.continuousOn)).neg
  have hAi : IntervalIntegrable (fun r => radialMassDensity n z r*deriv g r*deriv f r)
      MeasureTheory.volume 0 R := ((hM.mul hg.continuous_deriv_one).mul h1).intervalIntegrable
    (μ := MeasureTheory.volume) 0 R
  have hBi : IntervalIntegrable (fun r => g r*radialMassLaplacian n z f r)
      MeasureTheory.volume 0 R := (hg.continuous.continuousOn.mul hL).intervalIntegrable_of_Icc
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
  have hzero : radialMassDensity n z 0=0 := by simp [radialMassDensity]
  simp only [hzero,zero_mul,sub_zero] at he
  rw [intervalIntegral.integral_sub hAi hBi] at he
  linarith

end DefocusingNLS

end OAI
