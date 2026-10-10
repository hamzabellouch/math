import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialMassDivergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

namespace OAI

/-! Weighted integration by parts for the actual radial transport field. -/

open Set
open scoped ContDiff
namespace DefocusingNLS
open ProfileCertificate

theorem radialMassDensity_continuous (n : ℕ) (z : ProfileMatchingBall)
    (hX : HasRadialExterior (radialShootingNu (n+radialInnerShootingThreshold) z)
      (n+radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius))
    (hz : radialMatchingMap n z=0) : Continuous (radialMassDensity n z) := by
  have hQ := (radialMatchedProfile_differentiable n z hX hz).continuous
  exact (continuous_id.pow 11).mul (hQ.norm.pow 2)

theorem radialMassFlux_continuousOn (n : ℕ) (z : ProfileMatchingBall)
    (hX : HasRadialExterior (radialShootingNu (n+radialInnerShootingThreshold) z)
      (n+radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius))
    (hz : radialMatchingMap n z=0) (R : ℝ) :
    ContinuousOn (radialMassFlux n z) (Icc 0 R) := by
  let Q := radialMatchedProfile n z
  have hQ : ContinuousOn Q (Icc 0 R) :=
    (radialMatchedProfile_differentiable n z hX hz).continuous.continuousOn
  have hD := radialMatchedProfile_derivative_continuousOn n z hX hz R
  have hN := Complex.continuous_normSq.comp_continuousOn hQ
  have hJ := Complex.continuous_im.comp_continuousOn (hQ.star.mul hD)
  have hF : ContinuousOn (radialWeightedFlux Q) (Icc 0 R) :=
    ((continuous_id.div_const 2).continuousOn.mul hN).add (hJ.const_mul 2)
  have hc := (continuous_id.pow 11).continuousOn.mul hF
  apply hc.congr
  intro r hr
  exact radialMassFlux_eq n z hX hz r hr.1

theorem radialMatched_transport_integration (n : ℕ) (z : ProfileMatchingBall)
    (hX : HasRadialExterior (radialShootingNu (n+radialInnerShootingThreshold) z)
      (n+radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius))
    (hz : radialMatchingMap n z=0) (R : ℝ) (hR : 0 ≤ R)
    (f : ℝ → ℝ) (hf : ContDiff ℝ 1 f) (hfR : f R=0) :
    2*(∫ r in (0 : ℝ)..R, radialMassFlux n z r*f r*deriv f r)=
      -(6-2*radialShootingA n)*(∫ r in (0 : ℝ)..R, radialMassDensity n z r*(f r)^2) := by
  let A := fun r => radialMassDensity n z r*(f r)^2
  let B := fun r => radialMassFlux n z r*f r*deriv f r
  have hM := radialMassDensity_continuous n z hX hz
  have hF := radialMassFlux_continuousOn n z hX hz R
  have hfd := hf.continuous_deriv_one
  have hA : Continuous A := hM.mul (hf.continuous.pow 2)
  have hB : ContinuousOn B (Icc 0 R) := (hF.mul hf.continuous.continuousOn).mul hfd.continuousOn
  have hAi := hA.intervalIntegrable (μ := MeasureTheory.volume) 0 R
  have hBi := hB.intervalIntegrable_of_Icc (μ := MeasureTheory.volume) hR
  have hder (r : ℝ) (hr : r ∈ Ioo 0 R) :
      HasDerivAt (fun t => radialMassFlux n z t*(f t)^2)
        ((6-2*radialShootingA n)*A r+2*B r) r := by
    have h := (radialMassFlux_hasDerivAt n z hX hz r hr.1).mul
      (((hf.differentiable (by norm_num) r).hasDerivAt).pow 2)
    apply h.congr_deriv
    dsimp [A,B]
    norm_num only [Nat.cast_ofNat,Nat.reduceSub,pow_one]
    ring
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hR
    (hF.mul (hf.continuous.pow 2).continuousOn) hder
    ((hAi.const_mul (6-2*radialShootingA n)).add (hBi.const_mul 2))
  simp only [Pi.mul_apply,Pi.pow_apply,hfR,zero_pow (by norm_num : (2 : ℕ)≠0),mul_zero,
    radialMassFlux,radialMassDensity,zero_pow (by norm_num : (11 : ℕ)≠0),zero_mul,sub_zero] at he
  rw [intervalIntegral.integral_add (hAi.const_mul _) (hBi.const_mul 2),
    intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul] at he
  change 2*(∫ r in (0 : ℝ)..R, B r)=-(6-2*radialShootingA n)*(∫ r in (0 : ℝ)..R, A r)
  linarith

end DefocusingNLS

end OAI
