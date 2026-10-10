import OAI.Combinatorics.ExpectationThreshold.ThresholdCompactness
import OAI.Combinatorics.ExpectationThreshold.ThresholdBounds

namespace OAI

/-!
# Attainment of the integral and fractional thresholds

There are finitely many integral covers, so integral feasibility is closed
in the density interval. Fractional feasibility is a compact projection.
The actual suprema therefore belong to their respective feasible sets as
soon as those sets contain density zero.
-/

namespace TalagrandThreshold

open scoped BigOperators

variable {α : Type*} [Fintype α] [DecidableEq α]

omit [Fintype α] [DecidableEq α] in
theorem continuous_cost (G : Family α) : Continuous (fun p : ℝ => cost p G) := by
  unfold cost
  exact continuous_finsetSum G (fun S _ => continuous_pow S.card)

omit [DecidableEq α] in
/-- Smallness is a finite union of closed conditions, one per actual cover. -/
theorem isClosed_small (F : Family α) : IsClosed {p : ℝ | Small p F} := by
  classical
  have hset : {p : ℝ | Small p F} =
      ⋃ G : Family α, {p : ℝ | Covers G F ∧ cost p G ≤ 1 / 2} := by
    ext p
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Small]
  rw [hset]
  apply isClosed_iUnion_of_finite
  intro G
  by_cases hG : Covers G F
  · simpa only [hG, true_and] using
      (isClosed_le (continuous_cost G) (continuous_const :
        Continuous (fun _ : ℝ => (1 / 2 : ℝ))))
  · simpa only [hG, false_and, Set.ofPred_false] using
      (isClosed_empty : IsClosed (∅ : Set ℝ))

omit [DecidableEq α] in
theorem isCompact_integralFeasible (F : Family α) : IsCompact (integralFeasible F) := by
  have hset : integralFeasible F = Set.Icc (0 : ℝ) 1 ∩ {p : ℝ | Small p F} := by
    ext p
    constructor
    · intro hp
      exact ⟨⟨hp.1, hp.2.1⟩, hp.2.2⟩
    · intro hp
      exact ⟨hp.1.1, hp.1.2, hp.2⟩
  rw [hset]
  exact (isCompact_Icc : IsCompact (Set.Icc (0 : ℝ) 1)).inter_right (isClosed_small F)

omit [DecidableEq α] in
/-- The integral supremum is an actual feasible density. -/
theorem q_mem_integralFeasible (F : Family α) (hF : ∅ ∉ F) :
    q F ∈ integralFeasible F := by
  exact (isCompact_integralFeasible F).sSup_mem (integralFeasible_nonempty F hF)

/-- The fractional supremum is an actual feasible density. -/
theorem qf_mem_fractionalFeasible (F : Family α) (hF : ∅ ∉ F) :
    qf F ∈ fractionalFeasible F := by
  exact (isCompact_fractionalFeasible F).sSup_mem (fractionalFeasible_nonempty F hF)

omit [DecidableEq α] in
theorem small_q (F : Family α) (hF : ∅ ∉ F) : Small (q F) F :=
  (mem_integralFeasible.mp (q_mem_integralFeasible F hF)).2.2

theorem fractionalSmall_qf (F : Family α) (hF : ∅ ∉ F) : FractionalSmall (qf F) F :=
  (mem_fractionalFeasible.mp (qf_mem_fractionalFeasible F hF)).2.2

end TalagrandThreshold

end OAI
