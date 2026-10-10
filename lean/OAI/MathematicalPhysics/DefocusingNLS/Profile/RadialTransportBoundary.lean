import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialWeightedTransport

namespace OAI

/-! Weighted transport integration retaining the outgoing outer trace. -/

open Set
open scoped ContDiff
namespace DefocusingNLS
open ProfileCertificate

theorem radialMatched_weighted_transport_boundary (n : ℕ) (z : ProfileMatchingBall)
    (hX : HasRadialExterior (radialShootingNu (n+radialInnerShootingThreshold) z)
      (n+radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius))
    (hz : radialMatchingMap n z=0) (R : ℝ) (hR : 0 ≤ R)
    (q dq : ℝ → ℝ) (hq : ContinuousOn q (Icc 0 R)) (hdq : ContinuousOn dq (Icc 0 R))
    (hq' : ∀ r ∈ Ioo 0 R, HasDerivAt q (dq r) r)
    (f : ℝ → ℝ) (hf : ContDiff ℝ 1 f) :
    2*(∫ r in (0 : ℝ)..R, radialMassFlux n z r*q r*f r*deriv f r)=
      radialMassFlux n z R*q R*(f R)^2-
      (6-2*radialShootingA n)*(∫ r in (0 : ℝ)..R, radialMassDensity n z r*q r*(f r)^2)-
      (∫ r in (0 : ℝ)..R, radialMassFlux n z r*dq r*(f r)^2) := by
  let A := fun r => radialMassDensity n z r*q r*(f r)^2
  let B := fun r => radialMassFlux n z r*q r*f r*deriv f r
  let C := fun r => radialMassFlux n z r*dq r*(f r)^2
  have hM := radialMassDensity_continuous n z hX hz
  have hF := radialMassFlux_continuousOn n z hX hz R
  have hfd := hf.continuous_deriv_one
  have hA : ContinuousOn A (Icc 0 R) := (hM.continuousOn.mul hq).mul
    (hf.continuous.pow 2).continuousOn
  have hB : ContinuousOn B (Icc 0 R) :=
    ((hF.mul hq).mul hf.continuous.continuousOn).mul hfd.continuousOn
  have hC : ContinuousOn C (Icc 0 R) := (hF.mul hdq).mul
    (hf.continuous.pow 2).continuousOn
  have hAi := hA.intervalIntegrable_of_Icc (μ := MeasureTheory.volume) hR
  have hBi := hB.intervalIntegrable_of_Icc (μ := MeasureTheory.volume) hR
  have hCi := hC.intervalIntegrable_of_Icc (μ := MeasureTheory.volume) hR
  have hder (r : ℝ) (hr : r ∈ Ioo 0 R) :
      HasDerivAt (fun t => radialMassFlux n z t*q t*(f t)^2)
        (((6-2*radialShootingA n)*A r+C r)+2*B r) r := by
    have h := ((radialMassFlux_hasDerivAt n z hX hz r hr.1).mul (hq' r hr)).mul
      (((hf.differentiable (by norm_num) r).hasDerivAt).pow 2)
    apply h.congr_deriv
    dsimp [A,B,C]
    norm_num only [Nat.cast_ofNat,Nat.reduceSub,pow_one]
    ring
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hR
    ((hF.mul hq).mul (hf.continuous.pow 2).continuousOn) hder
    (((hAi.const_mul (6-2*radialShootingA n)).add hCi).add (hBi.const_mul 2))
  have hzero : radialMassFlux n z 0=0 := by simp [radialMassFlux,radialMassDensity]
  simp only [Pi.mul_apply,Pi.pow_apply,hzero,zero_mul,sub_zero] at he
  rw [intervalIntegral.integral_add ((hAi.const_mul _).add hCi) (hBi.const_mul 2),
    intervalIntegral.integral_add (hAi.const_mul _) hCi,
    intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul] at he
  change 2*(∫ r in (0 : ℝ)..R, B r)=
    radialMassFlux n z R*q R*(f R)^2-
    (6-2*radialShootingA n)*(∫ r in (0 : ℝ)..R, A r)-(∫ r in (0 : ℝ)..R, C r)
  linarith

theorem radialMatched_transport_boundary (n : ℕ) (z : ProfileMatchingBall)
    (hX : HasRadialExterior (radialShootingNu (n+radialInnerShootingThreshold) z)
      (n+radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius))
    (hz : radialMatchingMap n z=0) (R : ℝ) (hR : 0 ≤ R)
    (f : ℝ → ℝ) (hf : ContDiff ℝ 1 f) :
    2*(∫ r in (0 : ℝ)..R, radialMassFlux n z r*f r*deriv f r)=
      radialMassFlux n z R*(f R)^2-
      (6-2*radialShootingA n)*(∫ r in (0 : ℝ)..R, radialMassDensity n z r*(f r)^2) := by
  have hh := radialMatched_weighted_transport_boundary n z hX hz R hR
    (fun _ => 1) (fun _ => 0) continuousOn_const continuousOn_const
    (fun r _ => hasDerivAt_const r 1) f hf
  simpa only [mul_one,mul_zero,zero_mul,intervalIntegral.integral_zero,sub_zero] using hh

end DefocusingNLS

end OAI
