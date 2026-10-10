import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialAngularForms

namespace OAI

/-! Adding a spherical-harmonic eigenvalue to the regular scalar spectral forms. -/

open Set
open scoped ContDiff
namespace DefocusingNLS
open ProfileCertificate

noncomputable def radialAngularScalarAction (n : ℕ) (z : ProfileMatchingBall) (η : ℝ)
    (q f : ℝ → ℝ) (r : ℝ) : ℝ :=
  radialScalarAction n z q f r+η*radialAngularDensity n z r*f r

noncomputable def radialAngularScalarForm (n : ℕ) (z : ProfileMatchingBall) (η R : ℝ)
    (q f g : ℝ → ℝ) : ℝ :=
  radialScalarForm n z R q f g+η*radialAngularForm n z R f g

noncomputable def radialAngularScalarVirial (n : ℕ) (z : ProfileMatchingBall) (η R : ℝ)
    (q dq f : ℝ → ℝ) : ℝ :=
  radialScalarVirial n z R q dq f+η*radialAngularVirial n z R f

noncomputable def radialAngularScalarBoundary (n : ℕ) (z : ProfileMatchingBall) (η R s t : ℝ)
    (q f g : ℝ → ℝ) : ℝ :=
  radialSpectralBoundary n z R s t q f g+η*radialAngularBoundary n z R f

theorem radialAngularScalarForm_symm (n : ℕ) (z : ProfileMatchingBall) (η R : ℝ)
    (q f g : ℝ → ℝ) :
    radialAngularScalarForm n z η R q f g=radialAngularScalarForm n z η R q g f := by
  unfold radialAngularScalarForm
  rw [radialScalarForm_symm n z R q f g,radialAngularForm_symm n z R f g]

theorem radialAngularScalarAction_continuousOn (n : ℕ) (z : ProfileMatchingBall)
    (hX : HasRadialExterior (radialShootingNu (n+radialInnerShootingThreshold) z)
      (n+radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius))
    (hz : radialMatchingMap n z=0) (η R : ℝ) (q f : ℝ → ℝ)
    (hq : ContinuousOn q (Icc 0 R)) (hf : ContDiff ℝ 2 f) :
    ContinuousOn (radialAngularScalarAction n z η q f) (Icc 0 R) := by
  exact (radialScalarAction_continuousOn n z hX hz R q f hq hf).add
    (((radialAngularDensity_continuous n z hX hz).const_mul η).mul hf.continuous).continuousOn

theorem radialAngularScalarForm_spectralTest_boundary (n : ℕ) (z : ProfileMatchingBall)
    (hX : HasRadialExterior (radialShootingNu (n+radialInnerShootingThreshold) z)
      (n+radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius))
    (hz : radialMatchingMap n z=0) (η R s t : ℝ) (hR : 0 ≤ R)
    (q dq f g : ℝ → ℝ) (hq : ContinuousOn q (Icc 0 R))
    (hdq : ContinuousOn dq (Icc 0 R)) (hq' : ∀ r ∈ Ioo 0 R, HasDerivAt q (dq r) r)
    (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 1 g) :
    (∫ r in (0 : ℝ)..R,
      radialSpectralTest n z s t f g r*radialAngularScalarAction n z η q f r)=
      s*radialAngularScalarForm n z η R q f f+t*radialAngularScalarForm n z η R q f g+
        radialAngularScalarVirial n z η R q dq f+
          radialAngularScalarBoundary n z η R s t q f g := by
  have hT := radialSpectralTest_continuousOn n z hX hz R s t f g hf hg
  have hAi : IntervalIntegrable (fun r =>
      radialSpectralTest n z s t f g r*radialScalarAction n z q f r)
      MeasureTheory.volume 0 R :=
    (hT.mul (radialScalarAction_continuousOn n z hX hz R q f hq hf)).intervalIntegrable_of_Icc hR
  have hKi : IntervalIntegrable (fun r =>
      radialSpectralTest n z s t f g r*radialAngularDensity n z r*f r)
      MeasureTheory.volume 0 R :=
    ((hT.mul (radialAngularDensity_continuous n z hX hz).continuousOn).mul
      hf.continuous.continuousOn).intervalIntegrable_of_Icc hR
  have he : (∫ r in (0 : ℝ)..R,
      radialSpectralTest n z s t f g r*radialAngularScalarAction n z η q f r)=
      (∫ r in (0 : ℝ)..R, radialSpectralTest n z s t f g r*radialScalarAction n z q f r)+
      η*(∫ r in (0 : ℝ)..R, radialSpectralTest n z s t f g r*radialAngularDensity n z r*f r) := by
    calc
      _ = ∫ r in (0 : ℝ)..R,
          radialSpectralTest n z s t f g r*radialScalarAction n z q f r+
            η*(radialSpectralTest n z s t f g r*radialAngularDensity n z r*f r) := by
        apply intervalIntegral.integral_congr
        intro r _
        unfold radialAngularScalarAction
        ring
      _ = _ := by
        rw [intervalIntegral.integral_add hAi (hKi.const_mul η),intervalIntegral.integral_const_mul]
  rw [he,radialScalarForm_spectralTest_boundary n z hX hz R s t hR q dq f g hq hdq hq' hf hg,
    radialAngularForm_spectralTest n z hX hz R s t hR f g (hf.of_le (by norm_num)) hg.continuous]
  unfold radialAngularScalarForm radialAngularScalarVirial radialAngularScalarBoundary
  ring

end DefocusingNLS

end OAI
