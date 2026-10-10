import OAI.Analysis.CircleDomains.Sobolev.CircleDifferentialClosed
import OAI.Analysis.CircleDomains.Sobolev.ComplexCovectorWedge

namespace OAI

/-! The actual exterior derivative of a pulled-back smooth planar one-form.
This is a calculus identity used in the construction of Green's formula. -/
open Set Function
open scoped Topology ContDiff
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

def pulledPlanarForm (P Q : ℂ → ℝ) (F : (ℝ × ℝ) → ℂ)
    (v : ℝ × ℝ) (x : ℝ × ℝ) : ℝ :=
  P (F x) * ((fderiv ℝ F x) v).re + Q (F x) * ((fderiv ℝ F x) v).im


lemma pulledPlanarForm_contDiff {P Q : ℂ → ℝ} {F : (ℝ × ℝ) → ℂ}
    (hP : ContDiff ℝ ∞ P) (hQ : ContDiff ℝ ∞ Q) (hF : ContDiff ℝ ∞ F)
    (v : ℝ × ℝ) : ContDiff ℝ ∞ (pulledPlanarForm P Q F v) := by
  have hd := (hF.fderiv_right (m := ∞) (by simp)).clm_apply
    (contDiff_const (c := v))
  exact ((hP.comp hF).mul (Complex.reCLM.contDiff.comp hd)).add
    ((hQ.comp hF).mul (Complex.imCLM.contDiff.comp hd))

lemma pulledPlanarForm_fderiv {P Q : ℂ → ℝ} {F : (ℝ × ℝ) → ℂ}
    (hP : ContDiff ℝ ∞ P) (hQ : ContDiff ℝ ∞ Q) (hF : ContDiff ℝ ∞ F)
    (x v w : ℝ × ℝ) :
    (fderiv ℝ (pulledPlanarForm P Q F v) x) w =
      (fderiv ℝ P (F x)) ((fderiv ℝ F x) w) * ((fderiv ℝ F x) v).re +
      P (F x) * (((fderiv ℝ (fderiv ℝ F) x) w) v).re +
      ((fderiv ℝ Q (F x)) ((fderiv ℝ F x) w) * ((fderiv ℝ F x) v).im +
      Q (F x) * (((fderiv ℝ (fderiv ℝ F) x) w) v).im) := by
  have hFd : DifferentiableAt ℝ F x := hF.differentiable (by simp) x
  have hDF : DifferentiableAt ℝ (fderiv ℝ F) x :=
    (hF.contDiffAt.fderiv_right (m := 1) (by simp)).differentiableAt (by norm_num)
  have hv := hDF.hasFDerivAt.clm_apply (hasFDerivAt_const v x)
  have hpr := (hP.differentiable (by simp) (F x)).hasFDerivAt.comp x hFd.hasFDerivAt
  have hqr := (hQ.differentiable (by simp) (F x)).hasFDerivAt.comp x hFd.hasFDerivAt
  have hre := Complex.reCLM.hasFDerivAt.comp x hv
  have him := Complex.imCLM.hasFDerivAt.comp x hv
  have hh := (hpr.mul hre).add (hqr.mul him)
  change HasFDerivAt (fun y => P (F y) * ((fderiv ℝ F y) v).re +
    Q (F y) * ((fderiv ℝ F y) v).im) _ x at hh
  change (fderiv ℝ (fun y => P (F y) * ((fderiv ℝ F y) v).re +
    Q (F y) * ((fderiv ℝ F y) v).im) x) w = _
  rw [hh.fderiv]
  simp only [_root_.add_apply,_root_.smul_apply,
    ContinuousLinearMap.comp_apply,_root_.zero_apply,Function.comp_apply,
    ContinuousLinearMap.flip_apply,map_zero,zero_add,
    Complex.reCLM_apply,Complex.imCLM_apply,smul_eq_mul]
  ring

lemma pulledPlanarForm_curl {P Q : ℂ → ℝ} {F : (ℝ × ℝ) → ℂ}
    (hP : ContDiff ℝ ∞ P) (hQ : ContDiff ℝ ∞ Q) (hF : ContDiff ℝ ∞ F)
    (x : ℝ × ℝ) :
    (fderiv ℝ (pulledPlanarForm P Q F (0,1)) x) (1,0) -
      (fderiv ℝ (pulledPlanarForm P Q F (1,0)) x) (0,1) =
      ((((fderiv ℝ F x) (1,0)).re * ((fderiv ℝ F x) (0,1)).im -
        ((fderiv ℝ F x) (1,0)).im * ((fderiv ℝ F x) (0,1)).re) *
        ((fderiv ℝ Q (F x)) 1 - (fderiv ℝ P (F x)) Complex.I)) := by
  rw [pulledPlanarForm_fderiv hP hQ hF,pulledPlanarForm_fderiv hP hQ hF]
  have hsym := (hF.contDiffAt (x := x)).isSymmSndFDerivAt (by simp) (1,0) (0,1)
  rw [hsym]
  rw [complexCovector_apply (fderiv ℝ P (F x)) ((fderiv ℝ F x) (1,0)),
    complexCovector_apply (fderiv ℝ P (F x)) ((fderiv ℝ F x) (0,1)),
    complexCovector_apply (fderiv ℝ Q (F x)) ((fderiv ℝ F x) (1,0)),
    complexCovector_apply (fderiv ℝ Q (F x)) ((fderiv ℝ F x) (0,1))]
  ring

end CircleDomainRigidity

end

end OAI
