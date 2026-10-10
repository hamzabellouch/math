import OAI.Analysis.Nonexpansive.SwitchingTreeData
import OAI.Analysis.Nonexpansive.FiniteWitness
import OAI.Analysis.Nonexpansive.TreeTerminal
import OAI.Analysis.Nonexpansive.WeakCommonTerminal
import OAI.Analysis.Nonexpansive.FeasibleBranch

namespace OAI

/-!
# Finite witnesses from the actual constructed tree

The construction discharges the terminal, subtree, path, detector, and weighted
budget hypotheses of the finite switching argument using the actual tree data.
It keeps the chosen vector in the entire original-norm difference ball.
-/

noncomputable section

open Filter
open scoped Topology BigOperators Pointwise

namespace ReflexiveFixedPoints

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
variable {D : NormalizedMinimalData (X := X)}

namespace SwitchingTreeData

variable (A : SwitchingTreeData D)

/-- Forget the finite level bound without changing a node or its candidate label. -/
def truncationEmbedding (N : ℕ) (v : A.tree.TruncationNode N) : A.tree.NonrootNode :=
  ⟨v.1.val, v.2⟩

theorem truncationEmbedding_injective (N : ℕ) :
    Function.Injective (A.truncationEmbedding N) := by
  rintro ⟨⟨i, hi⟩, v⟩ ⟨⟨j, hj⟩, w⟩ h
  change (⟨i, v⟩ : A.tree.NonrootNode) = ⟨j, w⟩ at h
  obtain ⟨hij, hvw⟩ := Sigma.mk.inj_iff.mp h
  subst j
  have hvw' : v = w := eq_of_heq hvw
  subst w
  rfl

/-- Every finite truncation uses its original retained candidate budgets. -/
theorem finite_budget_le (N : ℕ) :
    (∑ v : A.tree.TruncationNode N, A.budget (v.1.val + 1) v.2) ≤
      (1 : ℝ) / 128 := by
  have h := OrderedTree.sum_retainedBudget_comp_le A.label A.label_injective
    (A.truncationEmbedding N) (A.truncationEmbedding_injective N)
  exact h.trans (by norm_num)

/-- One actual terminal resolvent satisfies every finite prediction detector
and the full displacement sum through the terminal level. -/
theorem exists_finite_terminal (N : ℕ) :
    ∃ j,
      (∀ v : A.tree.TruncationNode N,
        1 - 2 * A.budget (v.1.val + 1) v.2 ≤
          A.functionalAt (v.1.val + 1) v.2
            ((A.nodeLabel (v.1.val + 1) v.2 : X) -
              A.evaluation.evaluate (v.1.val + 1)
                (A.evaluation.idealCutoff (v.1.val + 1) A.anchor (A.terminal j) v.2))) ∧
      A.evaluation.terminalDefect (N + 1) (A.terminal j) ≤
        A.tree.cumulativeMinimum (OrderedTree.retainedBudget A.label) N := by
  let e : A.tree.TruncationNode N → ℝ :=
    fun v => A.budget (v.1.val + 1) v.2
  let a : A.tree.TruncationNode N → ℝ := fun v =>
    A.functional v.1.val v.2
      ((A.nodeLabel (v.1.val + 1) v.2 : X) - A.predictionLimit v.1.val v.2)
  let g : A.tree.TruncationNode N → ℕ → ℝ := fun v j =>
    A.functional v.1.val v.2
      ((A.nodeLabel (v.1.val + 1) v.2 : X) -
        A.evaluation.evaluate (v.1.val + 1)
          (A.evaluation.idealCutoff (v.1.val + 1) A.anchor (A.terminal j) v.2))
  have he : ∀ v, 0 < e v := fun v => A.budget_pos _ _
  have ha : ∀ v, 1 - e v ≤ a v := fun v => A.prediction_detector _ _
  have hg : ∀ v, Tendsto (g v) (A.ultrafilter : Filter ℕ) (𝓝 (a v)) := by
    intro v
    exact detector_tendsto_of_weak_tendsto (A.functional v.1.val v.2)
      (A.nodeLabel (v.1.val + 1) v.2) (A.predictionLimit v.1.val v.2)
      (fun j => A.evaluation.evaluate (v.1.val + 1)
        (A.evaluation.idealCutoff (v.1.val + 1) A.anchor (A.terminal j) v.2))
      (A.prediction_tendsto _ _)
  have hD : Tendsto (fun j => A.evaluation.terminalDefect (N + 1) (A.terminal j))
      atTop (𝓝 0) :=
    A.evaluation.terminalDefect_terminalSequence_tendsto D.closed D.convex D.T
      D.nonexpansive D.norm_sub_le_one A.generated A.anchor (N + 1)
  have hM : 0 < A.tree.cumulativeMinimum (OrderedTree.retainedBudget A.label) N :=
    A.tree.cumulativeMinimum_pos (OrderedTree.retainedBudget A.label)
      (OrderedTree.retainedBudget_pos A.label) N
  exact common_terminal_of_tendsto_mono A.ultrafilter_le_atTop e a g
    (fun j => A.evaluation.terminalDefect (N + 1) (A.terminal j))
    (A.tree.cumulativeMinimum (OrderedTree.retainedBudget A.label) N)
    he ha hg hD hM

/-- All of the actual finite tree's block detector inequalities hold at the
same selected terminal point. -/
theorem finite_block_detection (N j : ℕ)
    (hdet : ∀ v : A.tree.TruncationNode N,
      1 - 2 * A.budget (v.1.val + 1) v.2 ≤
        A.functionalAt (v.1.val + 1) v.2
          ((A.nodeLabel (v.1.val + 1) v.2 : X) -
            A.evaluation.evaluate (v.1.val + 1)
              (A.evaluation.idealCutoff (v.1.val + 1) A.anchor (A.terminal j) v.2)))
    (hD : A.evaluation.terminalDefect (N + 1) (A.terminal j) ≤
      A.tree.cumulativeMinimum (OrderedTree.retainedBudget A.label) N)
    (v : A.tree.TruncationNode N) :
    A.weights.pathWeight (v.1.val + 1) v.2 - 5 * A.budget (v.1.val + 1) v.2 ≤
      A.functionalAt (v.1.val + 1) v.2
        ((A.evaluation.beforeBlock v.levelBound (A.nodeLabel N) (A.terminal j) v.2 : X) -
          A.evaluation.afterBlock v.levelBound (A.nodeLabel N) (A.terminal j) v.2) := by
  have htail : (∑ d ∈ Finset.Ico (v.1.val + 1) N,
      A.tree.tolerance (OrderedTree.retainedBudget A.label) d) ≤
        A.budget (v.1.val + 1) v.2 :=
    A.tree.tolerance_tail_le_budget (OrderedTree.retainedBudget A.label)
      (OrderedTree.retainedBudget_pos A.label) (Nat.le_refl _) v.levelBound v.2
  have hterminal : A.evaluation.terminalDefect N (A.terminal j) ≤
      A.budget (v.1.val + 1) v.2 :=
    (A.evaluation.terminalDefect_le_succ N (A.terminal j)).trans
      (hD.trans (A.tree.cumulativeMinimum_le_budget
        (OrderedTree.retainedBudget A.label) v.levelBound v.2))
  exact A.evaluation.actual_block_detection D.norm_sub_le_one A.anchor (A.terminal j)
    (A.tree.tolerance (OrderedTree.retainedBudget A.label)) v.levelBound v.2
    (fun d _ p => A.child_average d p) (A.functionalAt (v.1.val + 1) v.2)
    (A.functionalAt_norm _ _) htail (A.path_displacement _ _) hterminal (hdet v)

/-- The actual normalized differences lie in the original difference span. -/
theorem difference_mem_span (_A : SwitchingTreeData D) (a b : D.K) :
    (a : X) - b ∈ differenceSpan D.K := by
  apply (Submodule.span ℝ (D.K - D.K)).le_topologicalClosure
  exact Submodule.subset_span (Set.sub_mem_sub a.property b.property)

/-- The constructed infinite tree has a whole-ball witness at every finite
depth.  Every central switching estimate has been discharged above. -/
theorem finite_witness (N : ℕ) :
    ∃ v : A.tree.Node N, ∃ d ∈ differenceBall D.K,
      A.tree.DetectsPrefix (fun k v x => A.functionalAt k v x) v d := by
  obtain ⟨j, hdet, hD⟩ := A.exists_finite_terminal N
  obtain ⟨s, hsY, hsNorm, hsDetect⟩ :=
    A.evaluation.finite_witness_of_block_detection N (A.nodeLabel N) (A.terminal j)
      (differenceSpan D.K) (A.difference_mem_span) D.norm_sub_le_one
      A.functionalAt A.functionalAt_norm
      (fun v => A.budget (v.1.val + 1) v.2) (A.finite_budget_le N)
      (A.finite_block_detection N j hdet hD)
  refine ⟨s, A.evaluation.switchVector N (A.nodeLabel N) (A.terminal j) s,
    ⟨hsY, hsNorm⟩, ?_⟩
  exact hsDetect

end SwitchingTreeData
end ReflexiveFixedPoints

end

end OAI
