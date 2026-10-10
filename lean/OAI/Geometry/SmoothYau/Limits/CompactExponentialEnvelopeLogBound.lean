import Mathlib

namespace OAI

noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace YauCounterexamples

lemma compact_exponential_envelope_log_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {K : Set E} (hK : IsCompact K) {φ : E → ℝ} (hφ : ContDiff ℝ ∞ φ) :
    ∃ H : ℝ, 0 ≤ H ∧ ∀ n : ℝ, 0 ≤ n → ∀ x ∈ K,
      ‖fderiv ℝ (fun y => Real.exp (n*φ y)) x‖ ≤ H*n*Real.exp (n*φ x) := by
  obtain ⟨C,hC⟩ := hK.exists_bound_of_continuousOn
    (hφ.fderiv_right (m:=∞) (by simp)).continuous.continuousOn
  refine ⟨max C 0,le_max_right _ _,?_⟩
  intro n hn x hx
  have hd := (((hφ.differentiable (by simp)) x).hasFDerivAt.const_mul n).exp.fderiv
  rw [hd,norm_smul,norm_smul,Real.norm_eq_abs,Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _),abs_of_nonneg hn]
  calc
    _ ≤ Real.exp (n*φ x)*(n* max C 0) := by gcongr; exact (hC x hx).trans (le_max_left _ _)
    _ = _ := by ring

end YauCounterexamples
end

end OAI
