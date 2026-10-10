import OAI.Combinatorics.EditApproximation.Geometry.ComparisonLiftBounds

namespace OAI

/-! Comparison paths below an arbitrary physical node retain their original
global table labels. No refinement program or random law is changed. -/

namespace EditApproximation

def treeLayerAppend {M k : ℕ} (initialPath : TreeLayer M k) :
    (d : ℕ) → TreeLayer M d → TreeLayer M (k + d)
  | 0, _ => initialPath
  | d + 1, path => (treeLayerAppend initialPath d path.1, path.2)

def physicalSubtreeNode {M J : ℕ} (root : PhysicalNode M J) (d : ℕ) (path : TreeLayer M d)
    (hd : root.1.val + d ≤ J) : PhysicalNode M J :=
  ⟨⟨root.1.val + d, by omega⟩, treeLayerAppend root.2 d path⟩

@[simp] theorem physicalSubtreeNode_zero {M J : ℕ} (root : PhysicalNode M J)
    (hd : root.1.val + 0 ≤ J) : physicalSubtreeNode root 0 PUnit.unit hd = root := by
  cases root
  rfl

theorem physicalSubtreeNode_child {M J : ℕ} (root : PhysicalNode M J)
    (d : ℕ) (path : TreeLayer M d) (hd : root.1.val + d < J) (i : Fin M) :
    physicalChild (physicalSubtreeNode root d path hd.le) hd i =
      physicalSubtreeNode root (d + 1) (path, i) (by omega) := rfl

theorem comparisonSubtree_active_source {α : Type*} (source target : List α)
    {M J : ℕ} (hM : 0 < M) (P : ℕ) (hP : 66 ≤ P)
    (root : PhysicalNode M J) (rootQ : TargetInterval target.length)
    (d : ℕ) (path : TreeLayer M d) (parent : TargetInterval source.length) (q : TargetInterval target.length)
    (heq : comparisonFrontier source target hM P hP
      (some (physicalSourceInterval source.length root, rootQ)) d path = some (parent, q))
    (hactive : ¬ comparisonStopped source target parent q) :
    parent = sourceIntervalAt M source.length (root.1.val + d) (treeLayerAppend root.2 d path) := by
  induction d generalizing parent q with
  | zero =>
    exact (congrArg Prod.fst (Option.some.inj heq)).symm
  | succ d ih =>
    obtain ⟨previousParent, previousQ, hprevious, hpreviousActive, hchild⟩ :=
      comparisonStep_active_parent source target hM P hP _ path.2 parent q heq hactive
    rw [ih path.1 previousParent previousQ hprevious hpreviousActive] at hchild
    exact hchild

noncomputable def comparisonSubtreeLift {α : Type*} {M J : ℕ} (source target : List α)
    (hM : 0 < M) (P : ℕ) (hP : 66 ≤ P) (table : PhysicalEntry M J target.length → ℝ)
    (root : PhysicalNode M J) (rootQ : TargetInterval target.length)
    (d : ℕ) (path : TreeLayer M d) : ℝ := by
  classical
  exact stoppedComparisonValue source target
    (if hd : root.1.val + d ≤ J then fun q => table (physicalSubtreeNode root d path hd, q) else fun _ => 0)
    (comparisonFrontier source target hM P hP (some (physicalSourceInterval source.length root, rootQ)) d path)

theorem comparisonSubtreeLift_root {α : Type*} {M J : ℕ} (source target : List α)
    (hM : 0 < M) (P : ℕ) (hP : 66 ≤ P) (table : PhysicalEntry M J target.length → ℝ)
    (hterminal : ∀ node q, comparisonStopped source target (physicalSourceInterval source.length node) q →
      table (node, q) = stateEditCost (physicalSource source node) target q)
    (root : PhysicalNode M J) (rootQ : TargetInterval target.length) :
    comparisonSubtreeLift source target hM P hP table root rootQ 0 PUnit.unit = table (root, rootQ) := by
  classical
  unfold comparisonSubtreeLift
  rw [dite_eq_left (by omega : root.1.val + 0 ≤ J), physicalSubtreeNode_zero]
  exact stoppedComparisonValue_physical source target table hterminal root rootQ

theorem comparisonSubtreeLift_step_active {α : Type*} {M J : ℕ} (source target : List α)
    (hM : 0 < M) (P : ℕ) (hP : 66 ≤ P) (table : PhysicalEntry M J target.length → ℝ)
    (hterminal : ∀ node q, comparisonStopped source target (physicalSourceInterval source.length node) q →
      table (node, q) = stateEditCost (physicalSource source node) target q)
    (root : PhysicalNode M J) (rootQ : TargetInterval target.length)
    (d : ℕ) (path : TreeLayer M d) (hd : root.1.val + d < J) (q : TargetInterval target.length)
    (hfrontier : comparisonFrontier source target hM P hP
      (some (physicalSourceInterval source.length root, rootQ)) d path =
        some (physicalSourceInterval source.length (physicalSubtreeNode root d path hd.le), q))
    (hactive : ¬ comparisonStopped source target
      (physicalSourceInterval source.length (physicalSubtreeNode root d path hd.le)) q) (i : Fin M) :
    let node := physicalSubtreeNode root d path hd.le
    let hc : 0 < stateEditCost (physicalSource source node) target q := by
      change 0 < stateEditCost (substring source (physicalSourceInterval source.length node).lo
        (physicalSourceInterval source.length node).hi) target q
      dsimp only [node]
      unfold comparisonStopped at hactive
      omega
    comparisonSubtreeLift source target hM P hP table root rootQ (d + 1) (path, i) =
      table (physicalChild node hd i,
        comparisonChildren source target hM P hP (physicalSourceInterval source.length node) q hc i) := by
  classical
  dsimp only
  unfold comparisonSubtreeLift
  rw [dite_eq_left (by omega : root.1.val + (d + 1) ≤ J)]
  change stoppedComparisonValue source target _
    (comparisonStep source target hM P hP
      (comparisonFrontier source target hM P hP _ d path) i) = _
  rw [hfrontier]
  simp only [comparisonStep, dite_eq_right hactive]
  rw [← physicalSubtreeNode_child root d path hd i]
  exact stoppedComparisonValue_physical source target table hterminal _ _

theorem comparisonSubtreeLift_terminal {α : Type*} {M J : ℕ} (source target : List α)
    (hM : 0 < M) (P : ℕ) (hP : 66 ≤ P) (table : PhysicalEntry M J target.length → ℝ)
    (root : PhysicalNode M J) (rootQ : TargetInterval target.length) (K : ℕ)
    (hheight : root.1.val + K = J) (hcapacity : source.length ≤ M ^ J) (path : TreeLayer M K) :
    comparisonSubtreeLift source target hM P hP table root rootQ K path =
      comparisonStateCost source target (comparisonFrontier source target hM P hP
        (some (physicalSourceInterval source.length root, rootQ)) K path) := by
  classical
  unfold comparisonSubtreeLift
  generalize heq : comparisonFrontier source target hM P hP
    (some (physicalSourceInterval source.length root, rootQ)) K path = state
  cases state with
  | none => rfl
  | some state =>
    rcases state with ⟨parent, q⟩
    have hstop : comparisonStopped source target parent q := by
      by_contra hactive
      have hp := comparisonSubtree_active_source source target hM P hP root rootQ K path parent q heq hactive
      have hcapacity' : source.length ≤ M ^ (root.1.val + K) := by rw [hheight]; exact hcapacity
      have hwidth := sourceIntervalAt_leaf_width M source.length (root.1.val + K) hM hcapacity'
        (treeLayerAppend root.2 K path)
      rw [← hp] at hwidth
      exact hactive (Or.inl hwidth)
    simp only [stoppedComparisonValue, ite_eq_left hstop, comparisonStateCost]

theorem comparisonSubtreeLift_mono {α : Type*} {M J : ℕ} (source target : List α)
    (hM : 0 < M) (P : ℕ) (hP : 66 ≤ P)
    (table table' : PhysicalEntry M J target.length → ℝ) (hle : table ≤ table')
    (root : PhysicalNode M J) (rootQ : TargetInterval target.length) (d : ℕ) (path : TreeLayer M d) :
    comparisonSubtreeLift source target hM P hP table root rootQ d path ≤
      comparisonSubtreeLift source target hM P hP table' root rootQ d path := by
  classical
  unfold comparisonSubtreeLift stoppedComparisonValue
  generalize comparisonFrontier source target hM P hP
    (some (physicalSourceInterval source.length root, rootQ)) d path = state
  cases state with
  | none => exact le_rfl
  | some state =>
    rcases state with ⟨parent, q⟩
    dsimp only
    split_ifs
    · exact le_rfl
    · exact hle _
    · exact le_rfl

theorem comparisonSubtreeLift_bounds {α : Type*} {M J : ℕ} (source target : List α)
    (hM : 0 < M) (P : ℕ) (hP : 66 ≤ P) (F : ℝ) (hF : 1 ≤ F)
    (table : PhysicalEntry M J target.length → ℝ)
    (htable : ∀ state, 0 ≤ table state ∧ table state ≤
      2 * F * stateEditCost (physicalSource source state.1) target state.2)
    (root : PhysicalNode M J) (rootQ : TargetInterval target.length) (d : ℕ) (path : TreeLayer M d) :
    0 ≤ comparisonSubtreeLift source target hM P hP table root rootQ d path ∧
      comparisonSubtreeLift source target hM P hP table root rootQ d path ≤
        2 * F * comparisonStateCost source target (comparisonFrontier source target hM P hP
          (some (physicalSourceInterval source.length root, rootQ)) d path) := by
  classical
  unfold comparisonSubtreeLift
  generalize heq : comparisonFrontier source target hM P hP
    (some (physicalSourceInterval source.length root, rootQ)) d path = state
  cases state with
  | none => simp only [stoppedComparisonValue, comparisonStateCost, mul_zero, le_refl, and_self]
  | some state =>
    rcases state with ⟨parent, q⟩
    by_cases hstop : comparisonStopped source target parent q
    · simp only [stoppedComparisonValue, ite_eq_left hstop, comparisonStateCost]
      refine ⟨Nat.cast_nonneg _, ?_⟩
      have h := mul_le_mul_of_nonneg_right (show (1 : ℝ) ≤ 2 * F by linarith) (Nat.cast_nonneg
        (stateEditCost (substring source parent.lo parent.hi) target q))
      simpa only [one_mul] using h
    · simp only [stoppedComparisonValue, ite_eq_right hstop, comparisonStateCost]
      split_ifs with hd
      · have hp := comparisonSubtree_active_source source target hM P hP root rootQ d path parent q heq hstop
        have h := htable (physicalSubtreeNode root d path hd, q)
        simpa only [physicalSource, physicalSourceInterval, physicalSubtreeNode, ← hp] using h
      · exact ⟨le_rfl, mul_nonneg (by linarith) (Nat.cast_nonneg _)⟩

theorem comparisonSubtreeLift_gap {α : Type*} {M J : ℕ} (source target : List α)
    (hM : 0 < M) (P : ℕ) (hP : 66 ≤ P)
    (table : PhysicalEntry M J target.length → ℝ)
    (htable : ∀ state, |stateLengthGap (physicalSource source state.1) target state.2| ≤ table state)
    (root : PhysicalNode M J) (rootQ : TargetInterval target.length)
    (d : ℕ) (hd : root.1.val + d ≤ J) (path : TreeLayer M d) :
    |comparisonStateGap source target (comparisonFrontier source target hM P hP
      (some (physicalSourceInterval source.length root, rootQ)) d path)| ≤
        comparisonSubtreeLift source target hM P hP table root rootQ d path := by
  classical
  unfold comparisonSubtreeLift
  rw [dite_eq_left hd]
  generalize heq : comparisonFrontier source target hM P hP
    (some (physicalSourceInterval source.length root, rootQ)) d path = state
  cases state with
  | none => simp only [comparisonStateGap, stoppedComparisonValue, abs_zero, le_refl]
  | some state =>
    rcases state with ⟨parent, q⟩
    by_cases hstop : comparisonStopped source target parent q
    · simp only [stoppedComparisonValue, ite_eq_left hstop, comparisonStateGap]
      exact stateEditCost_length_lower (substring source parent.lo parent.hi) target q
    · simp only [stoppedComparisonValue, ite_eq_right hstop, comparisonStateGap]
      have hp := comparisonSubtree_active_source source target hM P hP root rootQ d path parent q heq hstop
      have h := htable (physicalSubtreeNode root d path hd, q)
      simpa only [physicalSource, physicalSourceInterval, physicalSubtreeNode, ← hp] using h

end EditApproximation

end OAI
