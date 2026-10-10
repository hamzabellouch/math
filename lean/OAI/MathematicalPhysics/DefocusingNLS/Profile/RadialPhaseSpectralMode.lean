import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialSymmetryPhase
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialProfileDerivativeBounds
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialSpectralMode

namespace OAI

/-! The phase symmetry satisfies every regularity and integrability condition
retained for an actual radial spectral mode. -/

open Set MeasureTheory
open scoped ContDiff
namespace DefocusingNLS
open ProfileCertificate

private theorem iteratedDeriv_star_real (Q : ℝ → ℂ) (N : ℕ) :
    iteratedDeriv N (fun r => star (Q r))=fun r => star (iteratedDeriv N Q r) := by
  induction N with
  | zero => rfl
  | succ N ih => rw [iteratedDeriv_succ,ih,deriv.star',iteratedDeriv_succ]

noncomputable def radialMatchedPhaseMode (n : ℕ) (z : ProfileMatchingBall)
    (hX : HasRadialExterior (radialShootingNu (n+radialInnerShootingThreshold) z)
      (n+radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius))
    (hz : radialMatchingMap n z=0) (N : ℕ) (hN : 7≤N) :
    RadialSpectralMode (radialShootingA n) (radialShootingB (profileMatchingParameter z))
      (n+radialInnerShootingThreshold) N (radialMatchedProfile n z) 0 0 := by
  let Q := radialMatchedEvenProfile n z
  have hQ := radialMatchedEvenProfile_contDiff n z hX hz
  have hf : ContDiff ℝ ∞ (fun r => Complex.I*Q r) := contDiff_const.mul hQ
  have hg : ContDiff ℝ ∞ (fun r => -Complex.I*star (Q r)) :=
    contDiff_const.mul ((starL' ℝ : ℂ ≃L[ℝ] ℂ).contDiff.comp hQ)
  have htop := radialMatchedEvenProfile_top_integrable n z hX hz N hN
  refine ⟨(fun r => Complex.I*Q r),(fun r => -Complex.I*star (Q r)),
    hf.of_le (by norm_num),hg.of_le (by norm_num),radialMatched_phase_eigenpair n z hX hz,
    hf.contDiffOn,hg.contDiffOn,?_,?_,?_,?_⟩
  · simpa only [← smul_eq_mul,iteratedDeriv_fun_const_smul_field,norm_smul,
      Complex.norm_I,one_mul,one_smul] using htop
  · simpa only [← smul_eq_mul,iteratedDeriv_fun_const_smul_field,iteratedDeriv_star_real,
      norm_smul,norm_neg,Complex.norm_I,one_mul,one_smul,norm_star] using htop
  · obtain ⟨B,hB,hb⟩ := radialMatchedEvenProfile_bounded n z hX hz
    refine ⟨B,hB,?_⟩
    intro r
    simpa only [Prod.norm_mk,norm_mul,norm_neg,Complex.norm_I,one_mul,norm_star,
      max_self] using hb r
  · refine ⟨1,by norm_num,Or.inl (mul_ne_zero Complex.I_ne_zero ?_)⟩
    exact radialMatchedEvenProfile_ne_zero n z hX 1

end DefocusingNLS

end OAI
