import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Analysis.Normed.Group.Tannery

namespace OAI

/-! Bounded extensions of continuous functions with a bounded tail. -/

open Filter Set
open scoped BoundedContinuousFunction
namespace DefocusingNLS

variable {E : Type*} [NormedAddCommGroup E]

theorem continuous_halfLine_bound (f : ℝ → E) (hf : Continuous f)
    (h : ∃ C : ℝ, ∀ᶠ t in atTop, ‖f t‖ ≤ C) :
    ∃ M : ℝ, ∀ t, 0 ≤ t → ‖f t‖ ≤ M := by
  obtain ⟨C,hC⟩ := h
  obtain ⟨T,hT⟩ := eventually_atTop.mp hC
  obtain ⟨D,hD⟩ := (isCompact_Icc : IsCompact (Icc (0 : ℝ) (max T 0))).exists_bound_of_continuousOn
    hf.continuousOn
  refine ⟨max C D,?_⟩
  intro t ht
  by_cases hTt : T ≤ t
  · exact (hT t hTt).trans (le_max_left _ _)
  · exact (hD t ⟨ht,(le_of_lt (lt_of_not_ge hTt)).trans (le_max_left _ _)⟩).trans
      (le_max_right _ _)

theorem exists_bounded_extension_nonneg (f : ℝ → E) (hf : Continuous f)
    (h : ∃ C : ℝ, ∀ᶠ t in atTop, ‖f t‖ ≤ C) :
    ∃ F : ℝ →ᵇ E, ∀ t, 0 ≤ t → F t=f t := by
  obtain ⟨M,hM⟩ := continuous_halfLine_bound f hf h
  let F : ℝ →ᵇ E := BoundedContinuousFunction.ofNormedAddCommGroup
    (fun t => f (max t 0)) (hf.comp (continuous_id.max continuous_const)) M
      (fun t => hM _ (le_max_right t 0))
  refine ⟨F,?_⟩
  intro t ht
  change f (max t 0)=f t
  rw [max_eq_left ht]

theorem continuous_tendsto_halfLine_bounded (f : ℝ → E) (hf : Continuous f)
    (a : E) (ha : Tendsto f atTop (nhds a)) :
    ∃ F : ℝ →ᵇ E, ∀ t, 0 ≤ t → F t=f t := by
  apply exists_bounded_extension_nonneg f hf
  refine ⟨‖a‖+1,?_⟩
  filter_upwards [ha.norm.eventually (gt_mem_nhds (show ‖a‖<‖a‖+1 by linarith))] with t ht
  exact ht.le

end DefocusingNLS

end OAI
