import OAI.Analysis.Nonexpansive.TreeBudget
import OAI.Analysis.Nonexpansive.TreeTolerance

namespace OAI

/-!
# Conservative candidate scales imply the exact retained-budget tolerance

The construction may request a smaller return tolerance, using its complete
candidate counter. Every retained earlier ordinal is at most that counter,
so its geometric budget bounds this requested scale from below. The exposed
tolerance remains the exact dyadic multiple of the retained-budget minimum.
-/

namespace ReflexiveFixedPoints

theorem candidateBudget_antitone : Antitone candidateBudget := by
  intro m n hmn
  exact pow_le_pow_of_le_one
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) ≤ 1)
    (Nat.add_le_add_right hmn 9)

namespace OrderedTree

variable (T : OrderedTree) (label : T.NonrootNode → ℕ)

/-- A counter beyond all preceding labels supplies a lower bound for their
actual finite minimum. The zero-depth case is included. -/
theorem candidateBudget_le_cumulativeMinimum (k counter : ℕ)
    (hcounter : ∀ i < k, ∀ v : T.Node (i + 1), label ⟨i, v⟩ ≤ counter) :
    candidateBudget counter ≤ T.cumulativeMinimum (retainedBudget label) k := by
  apply (T.le_cumulativeMinimum_iff (retainedBudget label) k
    (candidateBudget counter)).2
  refine ⟨candidateBudget_le_one counter, ?_⟩
  intro i hi v
  exact candidateBudget_antitone (hcounter i hi v)

/-- The actual requested selection scale is no larger than the exact
retained-budget tolerance specified by the retained budgets. -/
theorem candidateScale_le_tolerance (k counter : ℕ)
    (hcounter : ∀ i < k, ∀ v : T.Node (i + 1), label ⟨i, v⟩ ≤ counter) :
    (1 / 2 : ℝ) ^ (k + 1) * candidateBudget counter ≤
      T.tolerance (retainedBudget label) k := by
  exact mul_le_mul_of_nonneg_left
    (T.candidateBudget_le_cumulativeMinimum label k counter hcounter)
    (pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) (k + 1))

/-- Strictly earlier candidate ordinals are a sufficient chronological bound. -/
theorem candidateScale_le_tolerance_of_lt (k counter : ℕ)
    (hcounter : ∀ i < k, ∀ v : T.Node (i + 1), label ⟨i, v⟩ < counter) :
    (1 / 2 : ℝ) ^ (k + 1) * candidateBudget counter ≤
      T.tolerance (retainedBudget label) k :=
  T.candidateScale_le_tolerance label k counter
    (fun i hi v => (hcounter i hi v).le)

end OrderedTree
end ReflexiveFixedPoints

end OAI
