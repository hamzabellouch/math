import OAI.Analysis.CircleDomains.Topology.PlanarFormPullback
import Mathlib.Analysis.SpecialFunctions.PolarCoord

namespace OAI

/-! Smoothness, differential, and oriented Jacobian of the actual complex
polar parametrization, including the radius-zero line. -/
open Set Function
open scoped Topology ContDiff
noncomputable section
namespace CircleDomainRigidity

lemma contDiff_complexPolarSymm : ContDiff ℝ ∞ (fun p => Complex.polarCoord.symm p) := by
  simp_rw [Complex.polarCoord_symm_apply]
  exact (Complex.ofRealCLM.contDiff.comp contDiff_fst).mul
    (((Complex.ofRealCLM.contDiff.comp (Real.contDiff_cos.comp contDiff_snd))).add
      ((Complex.ofRealCLM.contDiff.comp (Real.contDiff_sin.comp contDiff_snd)).mul (contDiff_const (c := Complex.I))))

lemma complexPolarSymm_fderiv (p v : ℝ × ℝ) :
    (fderiv ℝ (fun x => Complex.polarCoord.symm x) p) v =
      ((Real.cos p.2 * v.1 - p.1 * Real.sin p.2 * v.2 : ℝ) : ℂ) +
      ((Real.sin p.2 * v.1 + p.1 * Real.cos p.2 * v.2 : ℝ) : ℂ) * Complex.I := by
  have hd := Complex.equivRealProdCLM.symm.hasFDerivAt.comp p (hasFDerivAt_polarCoord_symm p)
  change HasFDerivAt (fun x => Complex.polarCoord.symm x) _ p at hd
  rw [hd.fderiv]
  simp [fderivPolarCoordSymm,Matrix.toLin_finTwoProd_toContinuousLinearMap,
    Complex.equivRealProdCLM_symm_apply,sub_eq_add_neg,mul_assoc]

lemma complexPolarSymm_jacobian (p : ℝ × ℝ) :
    ((fderiv ℝ (fun x => Complex.polarCoord.symm x) p) (1,0)).re *
        ((fderiv ℝ (fun x => Complex.polarCoord.symm x) p) (0,1)).im -
      ((fderiv ℝ (fun x => Complex.polarCoord.symm x) p) (1,0)).im *
        ((fderiv ℝ (fun x => Complex.polarCoord.symm x) p) (0,1)).re = p.1 := by
  simp only [complexPolarSymm_fderiv,Complex.add_re,Complex.add_im,Complex.ofReal_re,
    Complex.ofReal_im,Complex.mul_re,Complex.mul_im,Complex.I_re,Complex.I_im,
    mul_zero,mul_one,mul_neg,sub_zero,zero_add,add_zero,zero_sub]
  linear_combination p.1 * Real.sin_sq_add_cos_sq p.2

end CircleDomainRigidity

end

end OAI
