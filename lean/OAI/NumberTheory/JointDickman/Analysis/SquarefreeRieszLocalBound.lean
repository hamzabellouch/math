import OAI.NumberTheory.JointDickman.Analysis.SquarefreeRieszSingularFactor
import Mathlib.Analysis.Normed.Group.Bounded

namespace OAI

/-! # A fixed bounded neighborhood for the local Riesz kernel -/
namespace JointDickman
open Set Filter
open scoped Topology

theorem squarefreeRieszSingularFactor_local_bound {z : ℝ} (hz : 0 ≤ z) (hz1 : z ≤ 1) :
    ∃ r C : ℝ, 0 < r ∧ 0 ≤ C ∧
      ContinuousOn (fun t : ℝ => squarefreeRieszSingularFactor z (1-(t:ℂ))) (Icc 0 r) ∧
      ∀ t ∈ Icc 0 r, ‖squarefreeRieszSingularFactor z (1-(t:ℂ))‖ ≤ C := by
  obtain ⟨δ,hδ,hcont⟩ := Metric.eventually_nhds_iff.mp
    (squarefreeRieszSingularFactor_analyticAt_one hz hz1).eventually_continuousAt
  let r := δ/2
  have hr : 0 < r := by dsimp [r]; positivity
  have hf : ContinuousOn (fun t : ℝ => squarefreeRieszSingularFactor z (1-(t:ℂ))) (Icc 0 r) := by
    intro t ht
    have hd : dist (1-(t:ℂ)) 1 < δ := by
      rw [dist_eq_norm,sub_sub_cancel_left,norm_neg,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg ht.1]
      dsimp [r] at ht
      linarith [ht.2]
    exact (ContinuousAt.comp (f := fun t : ℝ => (1:ℂ)-(t:ℂ)) (hcont hd)
      (continuousAt_const.sub Complex.continuous_ofReal.continuousAt)).continuousWithinAt
  obtain ⟨C,hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hf
  exact ⟨r,max C 0,hr,le_max_right _ _,hf,fun t ht => (hC t ht).trans (le_max_left _ _)⟩

end JointDickman

end OAI
