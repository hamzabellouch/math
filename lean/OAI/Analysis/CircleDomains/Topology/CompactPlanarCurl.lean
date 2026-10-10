import OAI.Analysis.CircleDomains.Modulus.LocalizedNormalGreen
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

namespace OAI

/-! The integral of a compactly supported smooth derivative, and hence of
its planar curl, vanishes on the whole plane. -/
open Set Function MeasureTheory
open scoped Topology ContDiff
noncomputable section
namespace CircleDomainRigidity

lemma integral_compact_fderiv_eq_zero {f : ℂ → ℝ}
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) (v : ℂ) :
    (∫ z, (fderiv ℝ f z) v) = 0 := by
  have hd : Continuous (fun z => (fderiv ℝ f z) v) :=
    (hf.continuous_fderiv (by simp)).clm_apply continuous_const
  have hi : Integrable (fun z => (fderiv ℝ f z) v) volume := hd.integrable_of_hasCompactSupport (hc.fderiv_apply ℝ v)
  have he := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (μ := volume) (f := fun _ : ℂ => (1 : ℝ)) (g := f) (v := v)
    (by
      simp only [fderiv_const_apply,zero_apply,zero_mul]
      exact integrable_zero _ _ _)
    (by simpa only [one_mul] using hi)
    (by simpa only [one_mul] using hf.continuous.integrable_of_hasCompactSupport hc)
    (fun _ _ => differentiableAt_const _)
    (fun z _ => hf.differentiable (by simp) z)
  simpa only [one_mul,fderiv_const_apply,zero_apply,zero_mul,integral_zero,neg_zero] using he

lemma integral_compact_planar_curl {P Q : ℂ → ℝ}
    (hP : ContDiff ℝ ∞ P) (hQ : ContDiff ℝ ∞ Q)
    (hcP : HasCompactSupport P) (hcQ : HasCompactSupport Q) :
    (∫ z, (fderiv ℝ Q z) 1 - (fderiv ℝ P z) Complex.I) = 0 := by
  have hiP : Integrable (fun z => (fderiv ℝ P z) Complex.I) volume := ((hP.continuous_fderiv (by simp)).clm_apply
    (continuous_const (y := Complex.I))).integrable_of_hasCompactSupport (hcP.fderiv_apply ℝ _)
  have hiQ : Integrable (fun z => (fderiv ℝ Q z) 1) volume := ((hQ.continuous_fderiv (by simp)).clm_apply
    (continuous_const (y := (1 : ℂ)))).integrable_of_hasCompactSupport (hcQ.fderiv_apply ℝ _)
  rw [integral_sub hiQ hiP,integral_compact_fderiv_eq_zero hQ hcQ,
    integral_compact_fderiv_eq_zero hP hcP,sub_self]

end CircleDomainRigidity

end

end OAI
