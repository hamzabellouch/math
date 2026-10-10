import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialAngularScalar
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialSpectralCoercivity

namespace OAI

/-! The half-divergence shift cancels the pressure energy. Positive radial
and angular deformation control the remaining gradient energy. -/

open Set MeasureTheory
namespace DefocusingNLS
open ProfileCertificate

theorem radialShiftedVirial_coercive (n : ℕ) (z : ProfileMatchingBall)
    (hX : HasRadialExterior (radialShootingNu (n+radialInnerShootingThreshold) z)
      (n+radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius))
    (hz : radialMatchingMap n z=0) (eta R k C : ℝ) (heta : 0 ≤ eta) (hR : 0 ≤ R)
    (q dq f : ℝ → ℝ) (hf : ContDiff ℝ 1 f) (hdq : ContinuousOn dq (Icc 0 R))
    (hvel : ∀ r ∈ Icc 0 R, k ≤ deriv (radialMatchedVelocity n z) r ∧
      k ≤ radialMatchedVelocityRatio n z r)
    (hp : ∀ r ∈ Icc 0 R, radialMatchedVelocity n z r*dq r ≤ C) :
    k*radialAngularScalarForm n z eta R (fun _ => 0) f f ≤
      ((6-2*radialShootingA n)/2)*radialAngularScalarForm n z eta R q f f+
        radialAngularScalarVirial n z eta R q dq f+
        (C/2)*(∫ r in (0 : ℝ)..R, radialMassDensity n z r*(f r)^2) := by
  let a := (6-2*radialShootingA n)/2
  have hM := (radialMassDensity_continuous n z hX hz).continuousOn (s := Icc 0 R)
  have hD := radialDriftDensity_continuousOn n z hX hz R
  have hF := radialMassFlux_continuousOn n z hX hz R
  have hA := (radialAngularDensity_continuous n z hX hz).continuousOn (s := Icc 0 R)
  have hV := radialMatchedVelocityRatio_continuousOn n z hX hz R
  have hdf := hf.continuous_deriv_one.continuousOn (s := Icc 0 R)
  have hfc := hf.continuous.continuousOn (s := Icc 0 R)
  have hgrad : (k-a)*(∫ r in (0 : ℝ)..R, radialMassDensity n z r*(deriv f r)^2) ≤
      ∫ r in (0 : ℝ)..R, radialDriftDensity n z r*(deriv f r)^2 := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_mono_on hR
      (((hM.mul (hdf.pow 2)).const_mul (k-a)).intervalIntegrable_of_Icc hR)
      ((hD.mul (hdf.pow 2)).intervalIntegrable_of_Icc hR)
    intro r hr
    dsimp only [Pi.mul_apply,Pi.pow_apply]
    rw [radialDriftDensity_eq n z hX hz r hr.1]
    have hm : 0 ≤ radialMassDensity n z r := by
      have hr0 := hr.1
      dsimp only [radialMassDensity]
      positivity
    have hh := mul_le_mul_of_nonneg_right (hvel r hr).1 (mul_nonneg hm (sq_nonneg (deriv f r)))
    dsimp only [a]
    nlinarith only [hh]
  have hpress : (∫ r in (0 : ℝ)..R, radialMassFlux n z r*dq r*(f r)^2) ≤
      C*(∫ r in (0 : ℝ)..R, radialMassDensity n z r*(f r)^2) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_mono_on hR
      (((hF.mul hdq).mul (hfc.pow 2)).intervalIntegrable_of_Icc hR)
      (((hM.mul (hfc.pow 2)).const_mul C).intervalIntegrable_of_Icc hR)
    intro r hr
    dsimp only [Pi.mul_apply,Pi.pow_apply]
    have hm : 0 ≤ radialMassDensity n z r := by
      have hr0 := hr.1
      dsimp only [radialMassDensity]
      positivity
    have hh := mul_le_mul_of_nonneg_right (hp r hr) (mul_nonneg hm (sq_nonneg (f r)))
    change radialMassDensity n z r*radialMatchedVelocity n z r*dq r*(f r)^2 ≤ _
    nlinarith only [hh]
  have hang : k*radialAngularForm n z R f f ≤
      ∫ r in (0 : ℝ)..R, radialMatchedVelocityRatio n z r*radialAngularDensity n z r*(f r)^2 := by
    rw [radialAngularForm_diag,← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_mono_on hR
      (((hA.mul (hfc.pow 2)).const_mul k).intervalIntegrable_of_Icc hR)
      (((hV.mul hA).mul (hfc.pow 2)).intervalIntegrable_of_Icc hR)
    intro r hr
    dsimp only [Pi.mul_apply,Pi.pow_apply]
    have ha : 0 ≤ radialAngularDensity n z r := by
      have hr0 := hr.1
      dsimp only [radialAngularDensity]
      positivity
    have hh := mul_le_mul_of_nonneg_right (hvel r hr).2 (mul_nonneg ha (sq_nonneg (f r)))
    nlinarith only [hh]
  have hang' := mul_le_mul_of_nonneg_left hang heta
  dsimp only [radialAngularScalarForm,radialAngularScalarVirial,radialScalarVirial,radialAngularVirial]
  rw [radialScalarForm_diag,radialScalarForm_diag]
  simp only [mul_zero,zero_mul,intervalIntegral.integral_zero,add_zero]
  dsimp only [a] at hgrad
  nlinarith only [hgrad,hpress,hang']

end DefocusingNLS

end OAI
