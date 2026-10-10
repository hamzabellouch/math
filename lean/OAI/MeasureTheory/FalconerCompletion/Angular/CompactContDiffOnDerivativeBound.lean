import Mathlib
import OAI.MeasureTheory.FalconerCompletion.Sphere.SphereMeasure

namespace OAI

/-! Angular cutoffs and derivative estimates. -/

section
section
namespace Attempt4FullFar
open Set Metric
open scoped ContDiff Topology
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
lemma compact_contDiffOn_derivative_bound {f : E → F} {U K : Set E}
    (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U) (hf : ContDiffOn ℝ ∞ f U)
    (m : ℕ) : ∃ C : ℝ, 1 ≤ C ∧ ∀ j ≤ m, ∀ x ∈ K,
      ‖iteratedFDerivWithin ℝ j f U x‖ ≤ C := by
  have hbound (j : ℕ) : ∃ C : ℝ, ∀ x ∈ K,
      ‖iteratedFDerivWithin ℝ j f U x‖ ≤ C :=
    hK.exists_bound_of_continuousOn
      ((hf.continuousOn_iteratedFDerivWithin (by exact_mod_cast (le_top : (j:ℕ∞) ≤ ⊤)) hU.uniqueDiffOn).mono hKU)
  induction m with
  | zero =>
    obtain ⟨C,hC⟩ := hbound 0
    refine ⟨max 1 C, le_max_left _ _, ?_⟩
    intro j hj x hx
    have : j=0 := Nat.eq_zero_of_le_zero hj
    subst j
    exact (hC x hx).trans (le_max_right _ _)
  | succ m ih =>
    obtain ⟨D,hD,hboundD⟩ := ih
    obtain ⟨C,hC⟩ := hbound (m+1)
    refine ⟨max D C, hD.trans (le_max_left _ _), ?_⟩
    intro j hj x hx
    by_cases hjm : j ≤ m
    · exact (hboundD j hjm x hx).trans (le_max_left _ _)
    · have : j=m+1 := by omega
      subst j
      exact (hC x hx).trans (le_max_right _ _)

end Attempt4FullFar
end
end

end OAI
