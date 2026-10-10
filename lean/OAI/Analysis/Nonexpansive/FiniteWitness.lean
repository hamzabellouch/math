import OAI.Analysis.Nonexpansive.SwitchingBlocks
import OAI.Analysis.Nonexpansive.WeightedDeficit

namespace OAI

/-!
# A common path witness from actual block detection

Every vector in this finite argument is the normalized increment of the same
actual right-to-left switching experiment.  The construction of the terminal
point and the proof of block detection are supplied by the later tree-data
integration; they are not assumptions of the final fixed-point theorem.
-/

noncomputable section

open scoped BigOperators

namespace ReflexiveFixedPoints

namespace OrderedTree

/-- All nonroot nodes in a finite truncation, with their actual finite levels. -/
abbrev TruncationNode (T : OrderedTree) (N : ℕ) :=
  Σ k : Fin N, T.Node (k.val + 1)

namespace TruncationNode

variable {T : OrderedTree} {N : ℕ}

theorem levelBound (v : T.TruncationNode N) : v.1.val + 1 ≤ N :=
  Nat.succ_le_of_lt v.1.isLt

end TruncationNode
end OrderedTree

namespace TreeEvaluation

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
variable {T : OrderedTree} {W : WeightedTree T} {K : Set X}
variable (E : TreeEvaluation W K)

/-- Actual before/after block detection yields one leaf whose own normalized
root increment is detected at every nonroot point of its ancestor path.
There is no lower bound on the positive path weights. -/
theorem finite_witness_of_block_detection
    (N : ℕ) (y : T.Node N → K) (b : K)
    (Y : Submodule ℝ X) (hY : ∀ a c : K, (a : X) - c ∈ Y)
    (hdiam : ∀ a c : K, ‖(a : X) - c‖ ≤ 1)
    (f : (k : ℕ) → T.Node k → X →L[ℝ] ℝ)
    (hf : ∀ k v, ‖f k v‖ ≤ 1)
    (e : T.TruncationNode N → ℝ)
    (he : (∑ v, e v) ≤ (1 : ℝ) / 128)
    (hblock : ∀ v : T.TruncationNode N,
      W.pathWeight (v.1.val + 1) v.2 - 5 * e v ≤
        f (v.1.val + 1) v.2
          ((E.beforeBlock v.levelBound y b v.2 : X) -
            E.afterBlock v.levelBound y b v.2)) :
    ∃ s : T.Node N,
      E.switchVector N y b s ∈ Y ∧ ‖E.switchVector N y b s‖ ≤ 1 ∧
        ∀ i (hi : i ≤ N), 0 < i →
          (1 : ℝ) / 2 ≤ f i (T.ancestorLE hi s) (E.switchVector N y b s) := by
  classical
  let R : T.TruncationNode N → T.Node N → Prop :=
    fun v s => T.ancestorLE v.levelBound s = v.2
  let a : T.TruncationNode N → T.Node N → ℝ :=
    fun v s => f (v.1.val + 1) v.2 (E.switchVector N y b s)
  have hvector (s : T.Node N) :=
    E.switchVector_mem_norm_reconstruct N y b Y hY hdiam s
  have ha : ∀ v s, R v s → a v s ≤ 1 := by
    intro v s hrs
    exact functional_apply_le_one (f (v.1.val + 1) v.2)
      (hf _ _) (E.switchVector N y b s) (hvector s).2.1
  have hrow : ∀ v : T.TruncationNode N,
      (∑ s, if R v s then W.pathWeight N s * (1 - a v s) else 0) ≤ 5 * e v := by
    intro v
    have hv := block_deficit_of_detection
      (T.descendants v.levelBound v.2) (W.pathWeight N) (E.switchVector N y b)
      (f (v.1.val + 1) v.2).toLinearMap
      (E.beforeBlock v.levelBound y b v.2) (E.afterBlock v.levelBound y b v.2)
      (W.pathWeight (v.1.val + 1) v.2) (e v)
      (W.descendant_sum_pathWeight v.levelBound v.2)
      (E.switchVector_block_telescope v.levelBound y b v.2) (hblock v)
    simpa only [OrderedTree.descendants, Finset.sum_filter, R, a,
      ContinuousLinearMap.coe_coe] using hv
  obtain ⟨_, _, s, _, hgood⟩ := finite_weighted_deficit R (W.pathWeight N) e a
    (W.pathWeight_nonneg N) (W.sum_pathWeight N) ha hrow he
  refine ⟨s, (hvector s).1, (hvector s).2.1, ?_⟩
  intro i hi hipos
  cases i with
  | zero => omega
  | succ k =>
      have hk : k < N := Nat.lt_of_succ_le hi
      let v : T.TruncationNode N := ⟨⟨k, hk⟩, T.ancestorLE hi s⟩
      have hv : R v s := rfl
      exact le_of_lt (hgood v hv)

end TreeEvaluation
end ReflexiveFixedPoints

end

end OAI
