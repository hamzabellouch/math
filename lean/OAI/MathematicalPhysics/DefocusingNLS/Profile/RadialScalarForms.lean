import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialVirialEnergy
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialWeightedTransport

namespace OAI

/-! The scalar Green form and transport form used by the real spectral system. -/

open Set
open scoped ContDiff
namespace DefocusingNLS
open ProfileCertificate

noncomputable def radialScalarAction (n : ℕ) (z : ProfileMatchingBall)
    (q f : ℝ → ℝ) (r : ℝ) : ℝ :=
  radialMassLaplacian n z f r+radialMassDensity n z r*q r*f r

noncomputable def radialScalarForm (n : ℕ) (z : ProfileMatchingBall)
    (R : ℝ) (q f g : ℝ → ℝ) : ℝ :=
  (∫ r in (0 : ℝ)..R, radialMassDensity n z r*deriv f r*deriv g r)+
    ∫ r in (0 : ℝ)..R, radialMassDensity n z r*q r*f r*g r

theorem radialScalarForm_symm (n : ℕ) (z : ProfileMatchingBall)
    (R : ℝ) (q f g : ℝ → ℝ) :
    radialScalarForm n z R q f g=radialScalarForm n z R q g f := by
  unfold radialScalarForm
  congr 1 <;> apply intervalIntegral.integral_congr <;> intro r _ <;> ring

theorem radialScalarAction_continuousOn (n : ℕ) (z : ProfileMatchingBall)
    (hX : HasRadialExterior (radialShootingNu (n+radialInnerShootingThreshold) z)
      (n+radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius))
    (hz : radialMatchingMap n z=0) (R : ℝ) (q f : ℝ → ℝ)
    (hq : ContinuousOn q (Icc 0 R)) (hf : ContDiff ℝ 2 f) :
    ContinuousOn (radialScalarAction n z q f) (Icc 0 R) := by
  have hM := (radialMassDensity_continuous n z hX hz).continuousOn (s := Icc 0 R)
  have h1 := (hf.continuous_deriv (by norm_num)).continuousOn (s := Icc 0 R)
  have h2 := hf.deriv'.continuous_deriv_one.continuousOn (s := Icc 0 R)
  exact (((hM.mul h2).add ((radialMassSlope_continuousOn n z hX hz R).mul h1)).neg).add
    ((hM.mul hq).mul hf.continuous.continuousOn)

theorem radialScalarForm_Green (n : ℕ) (z : ProfileMatchingBall)
    (hX : HasRadialExterior (radialShootingNu (n+radialInnerShootingThreshold) z)
      (n+radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius))
    (hz : radialMatchingMap n z=0) (R : ℝ) (hR : 0 ≤ R)
    (q f g : ℝ → ℝ) (hq : ContinuousOn q (Icc 0 R))
    (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 1 g) (hgR : g R=0) :
    (∫ r in (0 : ℝ)..R, g r*radialScalarAction n z q f r)=
      radialScalarForm n z R q f g := by
  have hM := (radialMassDensity_continuous n z hX hz).continuousOn (s := Icc 0 R)
  have hL := radialScalarAction_continuousOn n z hX hz R (fun _ => 0) f
    continuousOn_const hf
  have hLi : IntervalIntegrable (fun r => g r*radialMassLaplacian n z f r)
      MeasureTheory.volume 0 R := by
    have hh := (hg.continuous.continuousOn.mul hL).intervalIntegrable_of_Icc
      (μ := MeasureTheory.volume) hR
    change IntervalIntegrable (fun r => g r*radialScalarAction n z (fun _ => 0) f r)
      MeasureTheory.volume 0 R at hh
    simpa only [radialScalarAction,mul_zero,zero_mul,add_zero] using hh
  have hqi : IntervalIntegrable (fun r => radialMassDensity n z r*q r*f r*g r)
      MeasureTheory.volume 0 R := (((hM.mul hq).mul hf.continuous.continuousOn).mul
    hg.continuous.continuousOn).intervalIntegrable_of_Icc (μ := MeasureTheory.volume) hR
  have he (r : ℝ) : g r*radialScalarAction n z q f r=
      g r*radialMassLaplacian n z f r+radialMassDensity n z r*q r*f r*g r := by
    unfold radialScalarAction
    ring
  simp_rw [he]
  rw [intervalIntegral.integral_add hLi hqi,
    radialMatched_Green_bilinear n z hX hz R hR f g hf hg hgR]
  unfold radialScalarForm
  congr 1
  apply intervalIntegral.integral_congr
  intro r _
  ring

theorem radialScalarForm_transport (n : ℕ) (z : ProfileMatchingBall)
    (hX : HasRadialExterior (radialShootingNu (n+radialInnerShootingThreshold) z)
      (n+radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius))
    (hz : radialMatchingMap n z=0) (R : ℝ) (hR : 0 ≤ R)
    (q dq f : ℝ → ℝ) (hq : ContinuousOn q (Icc 0 R))
    (hdq : ContinuousOn dq (Icc 0 R))
    (hq' : ∀ r ∈ Ioo 0 R, HasDerivAt q (dq r) r)
    (hf : ContDiff ℝ 2 f) (hfR : f R=0) (hdfR : deriv f R=0) :
    (∫ r in (0 : ℝ)..R, radialMatchedVelocity n z r*deriv f r*
      radialScalarAction n z q f r)=
      (∫ r in (0 : ℝ)..R, radialDriftDensity n z r*(deriv f r)^2)-
        (6-2*radialShootingA n)/2*(∫ r in (0 : ℝ)..R,
          radialMassDensity n z r*q r*(f r)^2)-
        (1/2)*(∫ r in (0 : ℝ)..R, radialMassFlux n z r*dq r*(f r)^2) := by
  have hM := (radialMassDensity_continuous n z hX hz).continuousOn (s := Icc 0 R)
  have hW := radialMatchedVelocity_continuousOn n z hX hz R
  have hL := radialScalarAction_continuousOn n z hX hz R (fun _ => 0) f continuousOn_const hf
  have h1 := (hf.continuous_deriv (by norm_num)).continuousOn (s := Icc 0 R)
  have hLi : IntervalIntegrable (fun r => radialMatchedVelocity n z r*deriv f r*
      radialMassLaplacian n z f r) MeasureTheory.volume 0 R := by
    have hh := ((hW.mul h1).mul hL).intervalIntegrable_of_Icc (μ := MeasureTheory.volume) hR
    change IntervalIntegrable (fun r => radialMatchedVelocity n z r*deriv f r*
      radialScalarAction n z (fun _ => 0) f r) MeasureTheory.volume 0 R at hh
    simpa only [radialScalarAction,mul_zero,zero_mul,add_zero] using hh
  have hqi : IntervalIntegrable (fun r => radialMassFlux n z r*q r*f r*deriv f r)
      MeasureTheory.volume 0 R := ((((radialMassFlux_continuousOn n z hX hz R).mul hq).mul
    hf.continuous.continuousOn).mul h1).intervalIntegrable_of_Icc (μ := MeasureTheory.volume) hR
  have he (r : ℝ) : radialMatchedVelocity n z r*deriv f r*radialScalarAction n z q f r=
      radialMatchedVelocity n z r*deriv f r*radialMassLaplacian n z f r+
        radialMassFlux n z r*q r*f r*deriv f r := by
    dsimp [radialScalarAction,radialMassFlux,radialMatchedVelocity]
    ring
  simp_rw [he]
  rw [intervalIntegral.integral_add hLi hqi,radialMatched_virial_energy n z hX hz R hR f hf hdfR]
  have ht := radialMatched_weighted_transport n z hX hz R hR q dq hq hdq hq'
    f (hf.of_le (by norm_num)) hfR
  linarith

end DefocusingNLS

end OAI
