import OAI.Analysis.Nonexpansive.SwitchingStates
import OAI.Analysis.Nonexpansive.OrderedTreeIntervals

namespace OAI

/-!
# Actual whole-block switches and their vector telescope

The ordered descendant interval determines the actual before/after root states.
All leaf increments come from the same cutoff experiment.
-/

noncomputable section

open scoped BigOperators

namespace ReflexiveFixedPoints

namespace OrderedTree

/-- Reindex a sum over an actual descendant fiber by its consecutive natural
interval. -/
theorem sum_descendants_eq_Ico (T : OrderedTree)
    {k N : ℕ} (h : k ≤ N) (v : T.Node k)
    {A : Type*} [AddCommMonoid A] (f : ℕ → A) :
    (∑ s ∈ T.descendants h v, f s.val) =
      ∑ i ∈ Finset.Ico (T.descendantLo h v) (T.descendantHi h v), f i := by
  classical
  apply Finset.sum_bij (fun s _ => s.val)
  · intro s hs
    exact Finset.mem_Ico.mpr
      ((T.ancestorLE_eq_iff_interval h v s).mp ((T.mem_descendants h v s).mp hs))
  · intro s hs t ht hst
    exact Fin.ext hst
  · intro i hi
    have hi' := Finset.mem_Ico.mp hi
    have him : i < T.size N := lt_of_lt_of_le hi'.2 (T.descendantHi_le_size h v)
    refine ⟨⟨i, him⟩, ?_, rfl⟩
    apply (T.mem_descendants h v _).mpr
    exact (T.ancestorLE_eq_iff_interval h v _).mpr hi'
  · intro s hs
    rfl

end OrderedTree

namespace TreeEvaluation

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
variable {T : OrderedTree} {W : WeightedTree T} {K : Set X}
variable (E : TreeEvaluation W K)

/-- The actual root just before the entire descendant block switches. -/
noncomputable def beforeBlock {k N : ℕ} (h : k ≤ N)
    (y : T.Node N → K) (b : K) (v : T.Node k) : K :=
  E.switchRoot N y b (T.descendantHi h v)

/-- The actual root just after the entire descendant block switches. -/
noncomputable def afterBlock {k N : ℕ} (h : k ≤ N)
    (y : T.Node N → K) (b : K) (v : T.Node k) : K :=
  E.switchRoot N y b (T.descendantLo h v)

/-- At the before-block cutoff, a leaf is unchanged exactly when its depth-k
ancestor is at or to the left of the block's node. -/
theorem switchLeaves_beforeBlock {k N : ℕ} (h : k ≤ N)
    (y : T.Node N → K) (b : K) (v : T.Node k) (s : T.Node N) :
    E.switchLeaves N y b (T.descendantHi h v) s =
      if T.ancestorLE h s ≤ v then y s else b := by
  simp only [switchLeaves, T.lt_descendantHi_iff_ancestorLE_le h v s]

/-- At the after-block cutoff, a leaf is unchanged exactly when its depth-k
ancestor is strictly to the left of the block's node. -/
theorem switchLeaves_afterBlock {k N : ℕ} (h : k ≤ N)
    (y : T.Node N → K) (b : K) (v : T.Node k) (s : T.Node N) :
    E.switchLeaves N y b (T.descendantLo h v) s =
      if T.ancestorLE h s < v then y s else b := by
  simp only [switchLeaves, T.lt_descendantLo_iff_ancestorLE_lt h v s]

/-- A node's own descendants are all unchanged immediately before its block. -/
theorem switchLeaves_beforeBlock_of_descendant {k N : ℕ} (h : k ≤ N)
    (y : T.Node N → K) (b : K) (v : T.Node k) (s : T.Node N)
    (hs : T.ancestorLE h s = v) :
    E.switchLeaves N y b (T.descendantHi h v) s = y s := by
  rw [E.switchLeaves_beforeBlock h y b v s, hs, ite_eq_left le_rfl]

/-- Multiplying the actual normalized increment by its positive path weight
recovers exactly the actual before-minus-after single-leaf difference. -/
theorem pathWeight_smul_switchVector (N : ℕ) (y : T.Node N → K) (b : K)
    (s : T.Node N) :
    W.pathWeight N s • E.switchVector N y b s =
      (E.switchRoot N y b (s.val + 1) : X) - E.switchRoot N y b s.val := by
  rw [switchVector, smul_smul, mul_inv_cancel₀ (ne_of_gt (W.pathWeight_pos N s)),
    one_smul]

/-- The sum of the actual normalized leaf increments over a descendant block
is exactly its actual before-minus-after root difference. -/
theorem switchVector_block_telescope {k N : ℕ} (h : k ≤ N)
    (y : T.Node N → K) (b : K) (v : T.Node k) :
    (∑ s ∈ T.descendants h v, W.pathWeight N s • E.switchVector N y b s) =
      (E.beforeBlock h y b v : X) - E.afterBlock h y b v := by
  calc
    (∑ s ∈ T.descendants h v, W.pathWeight N s • E.switchVector N y b s) =
        ∑ s ∈ T.descendants h v,
          ((E.switchRoot N y b (s.val + 1) : X) - E.switchRoot N y b s.val) := by
      apply Finset.sum_congr rfl
      intro s hs
      exact E.pathWeight_smul_switchVector N y b s
    _ = ∑ i ∈ Finset.Ico (T.descendantLo h v) (T.descendantHi h v),
          ((E.switchRoot N y b (i + 1) : X) - E.switchRoot N y b i) :=
      T.sum_descendants_eq_Ico h v
        (fun i => (E.switchRoot N y b (i + 1) : X) - E.switchRoot N y b i)
    _ = (E.beforeBlock h y b v : X) - E.afterBlock h y b v :=
      E.switchRoot_interval_telescope N y b (le_of_lt (T.descendantLo_lt_hi h v))

end TreeEvaluation
end ReflexiveFixedPoints

end

end OAI
