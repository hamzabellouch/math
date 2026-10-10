import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialAngularDensity
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialScalarBoundary

namespace OAI

/-! Angular potential transport, written with the regular density r^9 |Q|². -/

open Set
open scoped ContDiff
namespace DefocusingNLS
open ProfileCertificate

theorem radialAngular_transport (n : ℕ) (z : ProfileMatchingBall)
    (hX : HasRadialExterior (radialShootingNu (n+radialInnerShootingThreshold) z)
      (n+radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius))
    (hz : radialMatchingMap n z=0) (R : ℝ) (hR : 0 ≤ R)
    (f : ℝ → ℝ) (hf : ContDiff ℝ 1 f) :
    2*(∫ r in (0 : ℝ)..R, radialAngularDensity n z r*radialMatchedVelocity n z r*f r*deriv f r)=
      radialAngularDensity n z R*radialMatchedVelocity n z R*(f R)^2-
      (6-2*radialShootingA n)*(∫ r in (0 : ℝ)..R, radialAngularDensity n z r*(f r)^2)+
      2*(∫ r in (0 : ℝ)..R,
        radialMatchedVelocityRatio n z r*radialAngularDensity n z r*(f r)^2) := by
  let A := fun r => radialAngularDensity n z r*(f r)^2
  let B := fun r => radialAngularDensity n z r*radialMatchedVelocity n z r*f r*deriv f r
  let C := fun r => radialMatchedVelocityRatio n z r*radialAngularDensity n z r*(f r)^2
  have hK := radialAngularDensity_continuous n z hX hz
  have hW := radialMatchedVelocity_continuousOn n z hX hz R
  have hv := radialMatchedVelocityRatio_continuousOn n z hX hz R
  have hA : Continuous A := hK.mul (hf.continuous.pow 2)
  have hB : ContinuousOn B (Icc 0 R) :=
    ((hK.continuousOn.mul hW).mul hf.continuous.continuousOn).mul hf.continuous_deriv_one.continuousOn
  have hC : ContinuousOn C (Icc 0 R) :=
    (hv.mul hK.continuousOn).mul (hf.continuous.pow 2).continuousOn
  have hAi := hA.intervalIntegrable (μ := MeasureTheory.volume) 0 R
  have hBi := hB.intervalIntegrable_of_Icc (μ := MeasureTheory.volume) hR
  have hCi := hC.intervalIntegrable_of_Icc (μ := MeasureTheory.volume) hR
  have hder (r : ℝ) (hr : r ∈ Ioo 0 R) :
      HasDerivAt (fun t => radialAngularDensity n z t*radialMatchedVelocity n z t*(f t)^2)
        ((6-2*radialShootingA n)*A r-2*C r+2*B r) r := by
    have h := (radialAngularFlux_hasDerivAt n z hX hz r hr.1).mul
      (((hf.differentiable (by norm_num) r).hasDerivAt).pow 2)
    apply h.congr_deriv
    dsimp [A,B,C]
    norm_num only [Nat.cast_ofNat,Nat.reduceSub,pow_one]
    ring
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hR
    ((hK.continuousOn.mul hW).mul (hf.continuous.pow 2).continuousOn) hder
    (((hAi.const_mul (6-2*radialShootingA n)).sub (hCi.const_mul 2)).add (hBi.const_mul 2))
  simp only [Pi.mul_apply,Pi.pow_apply,radialAngularDensity,zero_pow (by norm_num : (9 : ℕ)≠0),zero_mul,sub_zero] at he
  rw [intervalIntegral.integral_add ((hAi.const_mul _).sub (hCi.const_mul 2)) (hBi.const_mul 2),
    intervalIntegral.integral_sub (hAi.const_mul _) (hCi.const_mul 2),
    intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul] at he
  change 2*(∫ r in (0 : ℝ)..R, B r)=
    radialAngularDensity n z R*radialMatchedVelocity n z R*(f R)^2-
      (6-2*radialShootingA n)*(∫ r in (0 : ℝ)..R, A r)+
        2*(∫ r in (0 : ℝ)..R, C r)
  dsimp only [radialAngularDensity]
  linarith

end DefocusingNLS

end OAI
