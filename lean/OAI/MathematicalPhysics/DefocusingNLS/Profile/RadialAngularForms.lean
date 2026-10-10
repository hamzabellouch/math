import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialAngularTransport

namespace OAI

/-! The angular part of the radial spectral form and its exact testing identity. -/

open Set
open scoped ContDiff
namespace DefocusingNLS
open ProfileCertificate

noncomputable def radialAngularForm (n : ℕ) (z : ProfileMatchingBall)
    (R : ℝ) (f g : ℝ → ℝ) : ℝ :=
  ∫ r in (0 : ℝ)..R, radialAngularDensity n z r*f r*g r

noncomputable def radialAngularVirial (n : ℕ) (z : ProfileMatchingBall)
    (R : ℝ) (f : ℝ → ℝ) : ℝ :=
  -((6-2*radialShootingA n)/2)*radialAngularForm n z R f f+
    ∫ r in (0 : ℝ)..R, radialMatchedVelocityRatio n z r*radialAngularDensity n z r*(f r)^2

noncomputable def radialAngularBoundary (n : ℕ) (z : ProfileMatchingBall)
    (R : ℝ) (f : ℝ → ℝ) : ℝ :=
  (1/2 : ℝ)*radialAngularDensity n z R*radialMatchedVelocity n z R*(f R)^2

theorem radialAngularForm_diag (n : ℕ) (z : ProfileMatchingBall) (R : ℝ) (f : ℝ → ℝ) :
    radialAngularForm n z R f f=∫ r in (0 : ℝ)..R, radialAngularDensity n z r*(f r)^2 := by
  unfold radialAngularForm
  apply intervalIntegral.integral_congr
  intro r _
  ring

theorem radialAngularForm_symm (n : ℕ) (z : ProfileMatchingBall) (R : ℝ) (f g : ℝ → ℝ) :
    radialAngularForm n z R f g=radialAngularForm n z R g f := by
  unfold radialAngularForm
  apply intervalIntegral.integral_congr
  intro r _
  ring

theorem radialAngularForm_nonneg (n : ℕ) (z : ProfileMatchingBall) (R : ℝ) (hR : 0 ≤ R)
    (f : ℝ → ℝ) : 0 ≤ radialAngularForm n z R f f := by
  rw [radialAngularForm_diag]
  apply intervalIntegral.integral_nonneg hR
  intro r hr
  have hr0 := hr.1
  unfold radialAngularDensity
  positivity

theorem radialAngularForm_spectralTest (n : ℕ) (z : ProfileMatchingBall)
    (hX : HasRadialExterior (radialShootingNu (n+radialInnerShootingThreshold) z)
      (n+radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius))
    (hz : radialMatchingMap n z=0) (R s t : ℝ) (hR : 0 ≤ R)
    (f g : ℝ → ℝ) (hf : ContDiff ℝ 1 f) (hg : Continuous g) :
    (∫ r in (0 : ℝ)..R,
      radialSpectralTest n z s t f g r*radialAngularDensity n z r*f r)=
      s*radialAngularForm n z R f f+t*radialAngularForm n z R f g+
        radialAngularVirial n z R f+radialAngularBoundary n z R f := by
  have hK := radialAngularDensity_continuous n z hX hz
  have hW := radialMatchedVelocity_continuousOn n z hX hz R
  have hA : IntervalIntegrable (fun r => radialAngularDensity n z r*f r*f r)
      MeasureTheory.volume 0 R := ((hK.mul hf.continuous).mul hf.continuous).intervalIntegrable 0 R
  have hB : IntervalIntegrable (fun r => radialAngularDensity n z r*f r*g r)
      MeasureTheory.volume 0 R := ((hK.mul hf.continuous).mul hg).intervalIntegrable 0 R
  have hC : IntervalIntegrable (fun r =>
      radialAngularDensity n z r*radialMatchedVelocity n z r*f r*deriv f r)
      MeasureTheory.volume 0 R :=
    (((hK.continuousOn.mul hW).mul hf.continuous.continuousOn).mul
      hf.continuous_deriv_one.continuousOn).intervalIntegrable_of_Icc hR
  have he : (∫ r in (0 : ℝ)..R,
      radialSpectralTest n z s t f g r*radialAngularDensity n z r*f r)=
      s*radialAngularForm n z R f f+t*radialAngularForm n z R f g+
        ∫ r in (0 : ℝ)..R, radialAngularDensity n z r*radialMatchedVelocity n z r*f r*deriv f r := by
    calc
      _ = ∫ r in (0 : ℝ)..R,
          (s*(radialAngularDensity n z r*f r*f r)+t*(radialAngularDensity n z r*f r*g r))+
            radialAngularDensity n z r*radialMatchedVelocity n z r*f r*deriv f r := by
        apply intervalIntegral.integral_congr
        intro r _
        unfold radialSpectralTest
        ring
      _ = _ := by
        rw [intervalIntegral.integral_add ((hA.const_mul s).add (hB.const_mul t)) hC,
          intervalIntegral.integral_add (hA.const_mul s) (hB.const_mul t),
          intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul]
        rfl
  have ht := radialAngular_transport n z hX hz R hR f hf
  rw [he]
  unfold radialAngularVirial radialAngularBoundary
  rw [radialAngularForm_diag]
  linarith

end DefocusingNLS

end OAI
