import Mathlib

namespace OAI

open Matrix

namespace CurrentKS.KKT
noncomputable section
open scoped Topology ContDiff

variable {A Z : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]

lemma partial_fderiv {F : A × Z → Z} {a : A} {z : Z} {L : Z →L[ℝ] Z}
    (hF : DifferentiableAt ℝ F (a,z))
    (hL : HasFDerivAt (fun v => F (a,v)) L z) :
    (fderiv ℝ F (a,z)).comp (ContinuousLinearMap.inr ℝ A Z) = L := by
  have hi : HasFDerivAt (fun v : Z => (a,v)) (ContinuousLinearMap.inr ℝ A Z) z := by
    convert (hasFDerivAt_const a z).prodMk (hasFDerivAt_id z) using 1 <;> rfl
  exact (hF.hasFDerivAt.comp z hi).unique hL

lemma smooth_branch [CompleteSpace A] [CompleteSpace Z] {F : A × Z → Z} {a : A} {z : Z}
    (hF : ContDiffAt ℝ ∞ F (a,z)) (J : Z ≃L[ℝ] Z)
    (hJ : HasFDerivAt (fun v => F (a,v)) J.toContinuousLinearMap z) :
    ∃ f : A → Z, f a = z ∧ ContDiffAt ℝ ∞ f a ∧
      ∀ᶠ b in 𝓝 a, F (b,f b) = F (a,z) := by
  have hi : ((fderiv ℝ F (a,z)).comp (ContinuousLinearMap.inr ℝ A Z)).IsInvertible := by
    rw [partial_fderiv (hF.differentiableAt (by simp)) hJ]
    exact ContinuousLinearMap.isInvertible_equiv
  refine ⟨hF.implicitFunction (by simp) hi, hF.implicitFunction_apply_self (by simp) hi,
    hF.contDiffAt_implicitFunction (by simp) hi, ?_⟩
  exact hF.eventually_apply_implicitFunction (by simp) hi

end
end CurrentKS.KKT

end OAI
