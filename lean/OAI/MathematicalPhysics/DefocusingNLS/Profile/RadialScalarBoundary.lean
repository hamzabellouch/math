import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialGreenBoundary
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialTransportBoundary
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialSpectralTesting

namespace OAI

/-! The scalar energy identities with the precise outgoing boundary terms. -/

open Set
open scoped ContDiff
namespace DefocusingNLS
open ProfileCertificate

theorem radialMatched_virial_boundary (n : ℕ) (z : ProfileMatchingBall)
    (hX : HasRadialExterior (radialShootingNu (n+radialInnerShootingThreshold) z)
      (n+radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius))
    (hz : radialMatchingMap n z=0) (R : ℝ) (hR : 0 ≤ R)
    (f : ℝ → ℝ) (hf : ContDiff ℝ 2 f) :
    (∫ r in (0 : ℝ)..R, radialMatchedVelocity n z r*deriv f r*
      radialMassLaplacian n z f r)=
        (∫ r in (0 : ℝ)..R, radialDriftDensity n z r*(deriv f r)^2)-
          (1/2)*radialMassFlux n z R*(deriv f R)^2 := by
  let B := fun r => radialMassFlux n z r*deriv f r*deriv (deriv f) r
  let C := fun r => radialMassSlope n z r*radialMatchedVelocity n z r*(deriv f r)^2
  let D := fun r => radialMassDensity n z r*(deriv f r)^2
  have hd : ContDiff ℝ 1 (deriv f) := hf.deriv'
  have h1 := hd.continuous
  have h2 := hd.continuous_deriv_one
  have hBi : IntervalIntegrable B MeasureTheory.volume 0 R := (((radialMassFlux_continuousOn n z hX hz R).mul h1.continuousOn).mul
    h2.continuousOn).intervalIntegrable_of_Icc (μ := MeasureTheory.volume) hR
  have hCi : IntervalIntegrable C MeasureTheory.volume 0 R := (((radialMassSlope_continuousOn n z hX hz R).mul
    (radialMatchedVelocity_continuousOn n z hX hz R)).mul
    (h1.pow 2).continuousOn).intervalIntegrable_of_Icc (μ := MeasureTheory.volume) hR
  have hDi : IntervalIntegrable D MeasureTheory.volume 0 R := ((radialMassDensity_continuous n z hX hz).mul (h1.pow 2)).intervalIntegrable
    (μ := MeasureTheory.volume) 0 R
  have hi (r : ℝ) : radialMatchedVelocity n z r*deriv f r*
      radialMassLaplacian n z f r= -B r-C r := by
    dsimp [B,C,radialMassLaplacian,radialMassFlux,radialMatchedVelocity]
    ring
  have ht := radialMatched_transport_boundary n z hX hz R hR (deriv f) hd
  change 2*(∫ r in (0 : ℝ)..R, B r)=radialMassFlux n z R*(deriv f R)^2-
    (6-2*radialShootingA n)*(∫ r in (0 : ℝ)..R, D r) at ht
  have he : (∫ r in (0 : ℝ)..R, radialDriftDensity n z r*(deriv f r)^2)=
      (6-2*radialShootingA n)/2*(∫ r in (0 : ℝ)..R, D r)-∫ r in (0 : ℝ)..R, C r := by
    have hh (r : ℝ) : radialDriftDensity n z r*(deriv f r)^2=
        (6-2*radialShootingA n)/2*D r-C r := by
      dsimp [radialDriftDensity,C,D]
      ring
    simp_rw [hh]
    rw [intervalIntegral.integral_sub (hDi.const_mul _) hCi,intervalIntegral.integral_const_mul]
  simp_rw [hi]
  have hsplit := intervalIntegral.integral_sub hBi.neg hCi
  simp only [Pi.neg_apply,intervalIntegral.integral_neg] at hsplit
  rw [hsplit,he]
  linarith

theorem radialScalarForm_Green_boundary (n : ℕ) (z : ProfileMatchingBall)
    (hX : HasRadialExterior (radialShootingNu (n+radialInnerShootingThreshold) z)
      (n+radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius))
    (hz : radialMatchingMap n z=0) (R : ℝ) (hR : 0 ≤ R)
    (q f g : ℝ → ℝ) (hq : ContinuousOn q (Icc 0 R))
    (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 1 g) :
    (∫ r in (0 : ℝ)..R, g r*radialScalarAction n z q f r)=
      radialScalarForm n z R q f g-radialMassDensity n z R*g R*deriv f R := by
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
    radialMatched_Green_boundary n z hX hz R hR f g hf hg]
  have hg' : (∫ r in (0 : ℝ)..R, radialMassDensity n z r*deriv g r*deriv f r)=
      ∫ r in (0 : ℝ)..R, radialMassDensity n z r*deriv f r*deriv g r := by
    apply intervalIntegral.integral_congr
    intro r _
    ring
  rw [hg']
  unfold radialScalarForm
  ring

theorem radialScalarForm_transport_boundary (n : ℕ) (z : ProfileMatchingBall)
    (hX : HasRadialExterior (radialShootingNu (n+radialInnerShootingThreshold) z)
      (n+radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius))
    (hz : radialMatchingMap n z=0) (R : ℝ) (hR : 0 ≤ R)
    (q dq f : ℝ → ℝ) (hq : ContinuousOn q (Icc 0 R))
    (hdq : ContinuousOn dq (Icc 0 R))
    (hq' : ∀ r ∈ Ioo 0 R, HasDerivAt q (dq r) r)
    (hf : ContDiff ℝ 2 f) :
    (∫ r in (0 : ℝ)..R, radialMatchedVelocity n z r*deriv f r*
      radialScalarAction n z q f r)=radialScalarVirial n z R q dq f+
        (1/2)*radialMassFlux n z R*(q R*(f R)^2-(deriv f R)^2) := by
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
      MeasureTheory.volume 0 R :=
    ((((radialMassFlux_continuousOn n z hX hz R).mul hq).mul
      hf.continuous.continuousOn).mul h1).intervalIntegrable_of_Icc (μ := MeasureTheory.volume) hR
  have he (r : ℝ) : radialMatchedVelocity n z r*deriv f r*radialScalarAction n z q f r=
      radialMatchedVelocity n z r*deriv f r*radialMassLaplacian n z f r+
        radialMassFlux n z r*q r*f r*deriv f r := by
    dsimp [radialScalarAction,radialMassFlux,radialMatchedVelocity]
    ring
  simp_rw [he]
  rw [intervalIntegral.integral_add hLi hqi,radialMatched_virial_boundary n z hX hz R hR f hf]
  have ht := radialMatched_weighted_transport_boundary n z hX hz R hR q dq hq hdq hq'
    f (hf.of_le (by norm_num))
  unfold radialScalarVirial
  nlinarith

noncomputable def radialSpectralBoundary (n : ℕ) (z : ProfileMatchingBall)
    (R s t : ℝ) (q f g : ℝ → ℝ) : ℝ :=
  (1/2)*radialMassFlux n z R*(q R*(f R)^2-(deriv f R)^2)-
    radialMassDensity n z R*(s*f R+t*g R)*deriv f R

theorem radialScalarForm_spectralTest_boundary (n : ℕ) (z : ProfileMatchingBall)
    (hX : HasRadialExterior (radialShootingNu (n+radialInnerShootingThreshold) z)
      (n+radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius))
    (hz : radialMatchingMap n z=0) (R s t : ℝ) (hR : 0 ≤ R)
    (q dq f g : ℝ → ℝ) (hq : ContinuousOn q (Icc 0 R))
    (hdq : ContinuousOn dq (Icc 0 R))
    (hq' : ∀ r ∈ Ioo 0 R, HasDerivAt q (dq r) r)
    (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 1 g) :
    (∫ r in (0 : ℝ)..R, radialSpectralTest n z s t f g r*radialScalarAction n z q f r)=
      s*radialScalarForm n z R q f f+t*radialScalarForm n z R q f g+
        radialScalarVirial n z R q dq f+radialSpectralBoundary n z R s t q f g := by
  let A := radialScalarAction n z q f
  have hA : ContinuousOn A (Icc 0 R) := radialScalarAction_continuousOn n z hX hz R q f hq hf
  have hFi : IntervalIntegrable (fun r => f r*A r) MeasureTheory.volume 0 R :=
    (hf.continuous.continuousOn.mul hA).intervalIntegrable_of_Icc (μ := MeasureTheory.volume) hR
  have hGi : IntervalIntegrable (fun r => g r*A r) MeasureTheory.volume 0 R :=
    (hg.continuous.continuousOn.mul hA).intervalIntegrable_of_Icc (μ := MeasureTheory.volume) hR
  have hWi : IntervalIntegrable (fun r => radialMatchedVelocity n z r*deriv f r*A r)
      MeasureTheory.volume 0 R :=
    (((radialMatchedVelocity_continuousOn n z hX hz R).mul
      (hf.continuous_deriv (by norm_num)).continuousOn).mul hA).intervalIntegrable_of_Icc
        (μ := MeasureTheory.volume) hR
  have he (r : ℝ) : radialSpectralTest n z s t f g r*A r=
      (s*(f r*A r)+t*(g r*A r))+radialMatchedVelocity n z r*deriv f r*A r := by
    unfold radialSpectralTest
    ring
  change (∫ r in (0 : ℝ)..R, radialSpectralTest n z s t f g r*A r)=_
  simp_rw [he]
  rw [intervalIntegral.integral_add ((hFi.const_mul s).add (hGi.const_mul t)) hWi,
    intervalIntegral.integral_add (hFi.const_mul s) (hGi.const_mul t),
    intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul]
  change s*(∫ r in (0 : ℝ)..R, f r*radialScalarAction n z q f r)+
    t*(∫ r in (0 : ℝ)..R, g r*radialScalarAction n z q f r)+
    (∫ r in (0 : ℝ)..R, radialMatchedVelocity n z r*deriv f r*radialScalarAction n z q f r)=_
  rw [radialScalarForm_Green_boundary n z hX hz R hR q f f hq hf (hf.of_le (by norm_num)),
    radialScalarForm_Green_boundary n z hX hz R hR q f g hq hf hg,
    radialScalarForm_transport_boundary n z hX hz R hR q dq f hq hdq hq' hf]
  unfold radialSpectralBoundary
  ring

end DefocusingNLS

end OAI
