import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialComplexScalarAction

namespace OAI

/-! The exact complex scalar virial formula is the sum of the two checked
real formulas, with the physical outer boundary retained. -/

open Set MeasureTheory
namespace DefocusingNLS
open ProfileCertificate

noncomputable def radialComplexAngularForm (n : ℕ) (z : ProfileMatchingBall)
    (eta R : ℝ) (q : ℝ → ℝ) (f : ℝ → ℂ) : ℝ :=
  radialAngularScalarForm n z eta R q (fun r => (f r).re) (fun r => (f r).re)+
    radialAngularScalarForm n z eta R q (fun r => (f r).im) (fun r => (f r).im)

noncomputable def radialComplexAngularVirial (n : ℕ) (z : ProfileMatchingBall)
    (eta R : ℝ) (q dq : ℝ → ℝ) (f : ℝ → ℂ) : ℝ :=
  radialAngularScalarVirial n z eta R q dq (fun r => (f r).re)+
    radialAngularScalarVirial n z eta R q dq (fun r => (f r).im)

noncomputable def radialComplexAngularBoundary (n : ℕ) (z : ProfileMatchingBall)
    (eta R s : ℝ) (q : ℝ → ℝ) (f : ℝ → ℂ) : ℝ :=
  radialAngularScalarBoundary n z eta R s 0 q (fun r => (f r).re) (fun r => (f r).re)+
    radialAngularScalarBoundary n z eta R s 0 q (fun r => (f r).im) (fun r => (f r).im)

theorem radialComplexAngular_virial_identity (n : ℕ) (z : ProfileMatchingBall)
    (hX : HasRadialExterior (radialShootingNu (n+radialInnerShootingThreshold) z)
      (n+radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius))
    (hz : radialMatchingMap n z=0) (eta R s : ℝ) (hR : 0 ≤ R)
    (q dq : ℝ → ℝ) (hq : ContinuousOn q (Icc 0 R)) (hdq : ContinuousOn dq (Icc 0 R))
    (hqd : ∀ r ∈ Ioo 0 R, HasDerivAt q (dq r) r) (f : ℝ → ℂ) (hf : ContDiff ℝ 2 f) :
    (∫ r in (0 : ℝ)..R, (star (radialComplexTest n z s f r)*
      radialComplexAngularAction n z eta q f r).re) =
      s*radialComplexAngularForm n z eta R q f+
        radialComplexAngularVirial n z eta R q dq f+
        radialComplexAngularBoundary n z eta R s q f := by
  have hfre : ContDiff ℝ 2 (fun r => (f r).re) := Complex.reCLM.contDiff.comp hf
  have hfim : ContDiff ℝ 2 (fun r => (f r).im) := Complex.imCLM.contDiff.comp hf
  have hr := radialAngularScalarForm_spectralTest_boundary n z hX hz eta R s 0 hR q dq
    (fun r => (f r).re) (fun r => (f r).re) hq hdq hqd hfre (hfre.of_le (by norm_num))
  have hi := radialAngularScalarForm_spectralTest_boundary n z hX hz eta R s 0 hR q dq
    (fun r => (f r).im) (fun r => (f r).im) hq hdq hqd hfim (hfim.of_le (by norm_num))
  have he r : (star (radialComplexTest n z s f r)*radialComplexAngularAction n z eta q f r).re =
      radialSpectralTest n z s 0 (fun t => (f t).re) (fun t => (f t).re) r*
        radialAngularScalarAction n z eta q (fun t => (f t).re) r+
      radialSpectralTest n z s 0 (fun t => (f t).im) (fun t => (f t).im) r*
        radialAngularScalarAction n z eta q (fun t => (f t).im) r := by
    simp only [Complex.mul_re,Complex.star_def,Complex.conj_re,Complex.conj_im,
      radialComplexTest_re n z s f (hf.differentiable (by norm_num)) r,
      radialComplexTest_im n z s f (hf.differentiable (by norm_num)) r,
      radialComplexAngularAction_re n z eta q f hf r,radialComplexAngularAction_im n z eta q f hf r]
    ring
  simp_rw [he]
  rw [intervalIntegral.integral_add]
  · rw [hr,hi]
    dsimp only [radialComplexAngularForm,radialComplexAngularVirial,radialComplexAngularBoundary]
    ring
  · exact ((radialSpectralTest_continuousOn n z hX hz R s 0 _ _ hfre (hfre.of_le (by norm_num))).mul
      (radialAngularScalarAction_continuousOn n z hX hz eta R q _ hq hfre)).intervalIntegrable_of_Icc hR
  · exact ((radialSpectralTest_continuousOn n z hX hz R s 0 _ _ hfim (hfim.of_le (by norm_num))).mul
      (radialAngularScalarAction_continuousOn n z hX hz eta R q _ hq hfim)).intervalIntegrable_of_Icc hR

end DefocusingNLS

end OAI
