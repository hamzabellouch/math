import Mathlib

namespace OAI

namespace WeakMTWGlobalSupport

section

open Filter
open scoped Topology ContDiff
namespace QuadraticHessian
variable {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

 theorem scalar_smooth (B : P → E →L[ℝ] E →L[ℝ] ℝ) (c : ℝ) {q : P}
    (hB : ContDiffAt ℝ ∞ B q) : ContDiffAt ℝ ∞ (fun z => c • B z) q := by
  exact hB.const_smul c

 theorem first (B : P → E →L[ℝ] E →L[ℝ] ℝ) (ν : P → E) {q : P}
    (hB : DifferentiableAt ℝ B q) (hν : DifferentiableAt ℝ ν q) (k : P) :
    fderiv ℝ (fun z => B z (ν z) (ν z)) q k =
      fderiv ℝ B q k (ν q) (ν q) + B q (fderiv ℝ ν q k) (ν q) +
        B q (ν q) (fderiv ℝ ν q k) := by
  rw [fderiv_clm_apply (hB.clm_apply hν) hν, fderiv_clm_apply hB hν]
  simp only [add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply]
  abel

 theorem second_zero (B : P → E →L[ℝ] E →L[ℝ] ℝ) (ν : P → E) {q : P}
    (hB : ContDiffAt ℝ 2 B q) (hν : ContDiffAt ℝ 2 ν q) (hz : ν q = 0) (h k : P) :
    fderiv ℝ (fun z => fderiv ℝ (fun y => B y (ν y) (ν y)) z k) q h =
      B q (fderiv ℝ ν q h) (fderiv ℝ ν q k) +
        B q (fderiv ℝ ν q k) (fderiv ℝ ν q h) := by
  have hb := hB.differentiableAt (by norm_num)
  have hv := hν.differentiableAt (by norm_num)
  have hdb : DifferentiableAt ℝ (fun z => fderiv ℝ B z k) q :=
    ((hB.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).clm_apply
      (differentiableAt_const k)
  have hdv : DifferentiableAt ℝ (fun z => fderiv ℝ ν z k) q :=
    ((hν.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).clm_apply
      (differentiableAt_const k)
  have he : (fun z => fderiv ℝ (fun y => B y (ν y) (ν y)) z k) =ᶠ[𝓝 q]
      (fun z => fderiv ℝ B z k (ν z) (ν z) + B z (fderiv ℝ ν z k) (ν z) +
        B z (ν z) (fderiv ℝ ν z k)) := by
    filter_upwards [hB.eventually (by norm_num), hν.eventually (by norm_num)] with z hb hv
    exact first B ν (hb.differentiableAt (by norm_num)) (hv.differentiableAt (by norm_num)) k
  rw [he.fderiv_eq]
  have h1 := (hdb.hasFDerivAt.clm_apply hv.hasFDerivAt).clm_apply hv.hasFDerivAt
  have h2 := (hb.hasFDerivAt.clm_apply hdv.hasFDerivAt).clm_apply hv.hasFDerivAt
  have h3 := (hb.hasFDerivAt.clm_apply hv.hasFDerivAt).clm_apply hdv.hasFDerivAt
  have hh := congrArg (fun L : P →L[ℝ] ℝ => L h) ((h1.fun_add h2).fun_add h3).fderiv
  rw [hh]
  simp [hz, add_comm]

end QuadraticHessian
end

end WeakMTWGlobalSupport

end OAI
