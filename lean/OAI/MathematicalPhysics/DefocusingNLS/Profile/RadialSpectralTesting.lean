import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialScalarForms

namespace OAI

/-! Testing the complexified radial spectral equation in real coordinates. -/

open Set
open scoped ContDiff
namespace DefocusingNLS
open ProfileCertificate

noncomputable def radialScalarVirial (n : ℕ) (z : ProfileMatchingBall)
    (R : ℝ) (q dq f : ℝ → ℝ) : ℝ :=
  (∫ r in (0 : ℝ)..R, radialDriftDensity n z r*(deriv f r)^2)-
    (6-2*radialShootingA n)/2*(∫ r in (0 : ℝ)..R, radialMassDensity n z r*q r*(f r)^2)-
    (1/2)*(∫ r in (0 : ℝ)..R, radialMassFlux n z r*dq r*(f r)^2)

noncomputable def radialSpectralTest (n : ℕ) (z : ProfileMatchingBall)
    (s t : ℝ) (f g : ℝ → ℝ) (r : ℝ) : ℝ :=
  s*f r+t*g r+radialMatchedVelocity n z r*deriv f r

theorem radialSpectralTest_continuousOn (n : ℕ) (z : ProfileMatchingBall)
    (hX : HasRadialExterior (radialShootingNu (n+radialInnerShootingThreshold) z)
      (n+radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius))
    (hz : radialMatchingMap n z=0) (R s t : ℝ) (f g : ℝ → ℝ)
    (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 1 g) :
    ContinuousOn (radialSpectralTest n z s t f g) (Icc 0 R) :=
  ((hf.continuous.continuousOn.const_mul s).add (hg.continuous.continuousOn.const_mul t)).add
    ((radialMatchedVelocity_continuousOn n z hX hz R).mul
      (hf.continuous_deriv (by norm_num)).continuousOn)

theorem radialScalarForm_spectralTest (n : ℕ) (z : ProfileMatchingBall)
    (hX : HasRadialExterior (radialShootingNu (n+radialInnerShootingThreshold) z)
      (n+radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius))
    (hz : radialMatchingMap n z=0) (R s t : ℝ) (hR : 0 ≤ R)
    (q dq f g : ℝ → ℝ) (hq : ContinuousOn q (Icc 0 R))
    (hdq : ContinuousOn dq (Icc 0 R))
    (hq' : ∀ r ∈ Ioo 0 R, HasDerivAt q (dq r) r)
    (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 1 g)
    (hfR : f R=0) (hdfR : deriv f R=0) (hgR : g R=0) :
    (∫ r in (0 : ℝ)..R, radialSpectralTest n z s t f g r*radialScalarAction n z q f r)=
      s*radialScalarForm n z R q f f+t*radialScalarForm n z R q f g+
        radialScalarVirial n z R q dq f := by
  let A := radialScalarAction n z q f
  have hA : ContinuousOn A (Icc 0 R) := radialScalarAction_continuousOn n z hX hz R q f hq hf
  have hFi : IntervalIntegrable (fun r => f r*A r) MeasureTheory.volume 0 R := (hf.continuous.continuousOn.mul hA).intervalIntegrable_of_Icc
    (μ := MeasureTheory.volume) hR
  have hGi : IntervalIntegrable (fun r => g r*A r) MeasureTheory.volume 0 R := (hg.continuous.continuousOn.mul hA).intervalIntegrable_of_Icc
    (μ := MeasureTheory.volume) hR
  have hWi : IntervalIntegrable (fun r => radialMatchedVelocity n z r*deriv f r*A r)
      MeasureTheory.volume 0 R := (((radialMatchedVelocity_continuousOn n z hX hz R).mul
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
  rw [radialScalarForm_Green n z hX hz R hR q f f hq hf (hf.of_le (by norm_num)) hfR,
    radialScalarForm_Green n z hX hz R hR q f g hq hf hg hgR,
    radialScalarForm_transport n z hX hz R hR q dq f hq hdq hq' hf hfR hdfR]
  rfl

theorem radialSkewPair_cancellation (M A B C D x y u v : ℝ)
    (h1 : A+M*u=0) (h2 : B+M*v=0) (h3 : C-M*x=0) (h4 : D-M*y=0) :
    (x*A+y*B)+(u*C+v*D)=0 := by
  linear_combination x*h1+y*h2+u*h3+v*h4

end DefocusingNLS

end OAI
