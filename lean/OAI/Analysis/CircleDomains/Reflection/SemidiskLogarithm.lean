import OAI.Analysis.CircleDomains.Reflection.SemidiskContinuousExtension
import Mathlib.Analysis.Complex.BranchLogRoot
import Mathlib.Analysis.Convex.Contractible

namespace OAI

/-! A genuine holomorphic logarithm on the half disk. Its imaginary
coordinate records only the modulus of the original function. -/
open Set Function Filter Complex
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

lemma exists_semidisk_logarithm {R : ℝ} {f : ℂ → ℂ} (hR : 0<R)
    (hd : DifferentiableOn ℂ f (upperSemidisk R))
    (hn : ∀z∈upperSemidisk R,f z≠0) :
    ∃g:ℂ→ℂ,DifferentiableOn ℂ g (upperSemidisk R) ∧
      (∀z∈upperSemidisk R,exp (I*g z)=f z) ∧
      (∀z∈upperSemidisk R,(g z).im= -Real.log ‖f z‖) := by
  have hU := upperSemidisk_open R
  have hsim : IsSimplyConnected (upperSemidisk R) := by
    let : ContractibleSpace (upperSemidisk R) :=
      (upperSemidisk_convex R).contractibleSpace (upperSemidisk_nonempty hR)
    change SimplyConnectedSpace (upperSemidisk R)
    infer_instance
  obtain ⟨L,hL,hLeq⟩ := exists_continuousOn_eqOn_exp_comp hsim hU hd.continuousOn
    (by rintro ⟨z,hz,he⟩;exact hn z hz he)
  have hLd : DifferentiableOn ℂ L (upperSemidisk R) := by
    intro z hz
    have heq : exp ∘ L =ᶠ[𝓝 z] f := by
      filter_upwards [hU.mem_nhds hz] with w hw
      exact hLeq hw
    exact (HasDerivAt.of_comp_left (hL.continuousAt (hU.mem_nhds hz))
      (hasDerivAt_exp (L z)) ((hd z hz).differentiableAt (hU.mem_nhds hz)).hasDerivAt
      (exp_ne_zero _) heq).differentiableAt.differentiableWithinAt
  refine ⟨fun z => -I*L z,?_,?_,?_⟩
  · exact hLd.const_mul (-I)
  · intro z hz
    have he : I*(-I*L z)=L z := by rw [←mul_assoc,mul_neg,I_mul_I,neg_neg,one_mul]
    rw [he]
    exact hLeq hz
  · intro z hz
    have he : exp (L z)=f z := hLeq hz
    have hnorm := congrArg norm he
    rw [norm_exp] at hnorm
    have hlog := congrArg Real.log hnorm
    rw [Real.log_exp] at hlog
    simpa only [neg_mul,neg_im,I_mul_im] using congrArg Neg.neg hlog

end CircleDomainRigidity

end

end OAI
