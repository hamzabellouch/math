import OAI.Combinatorics.MatrixRemoval.Host
import OAI.Combinatorics.MatrixRemoval.TreePositions

namespace OAI

/-!
Comparison lemmas for the concrete depth-first tree orders used in
mode localization.
-/

namespace Problem348.Construction

open TreePositions

theorem eq_plusPos_of_atLevel {h i : ℕ} {v : VariablePosition h}
    (hv : AtLevel i true v) :
    v = TreePositions.plusPos i (hv.1 ▸ depth_le v) v.2 := by
  apply Prod.ext
  · apply Fin.ext
    have hc := v.1.isLt
    obtain ⟨hd, hs⟩ := hv
    simp only [depth] at hd
    change v.1.val = 2 * i
    rcases hs with hi | hs
    · omega
    · simp only [plus, decide_eq_true_eq] at hs
      omega
  · rfl

theorem eq_minusPos_of_atLevel {h i : ℕ} {v : VariablePosition h}
    (hv : AtLevel i false v) :
    v = TreePositions.minusPos i (hv.1 ▸ depth_le v) v.2 := by
  apply Prod.ext
  · apply Fin.ext
    have hc := v.1.isLt
    obtain ⟨hd, hs⟩ := hv
    simp only [depth] at hd
    change v.1.val = if i = h then 2 * h else 2 * i + 1
    split_ifs with hi
    · omega
    · rcases hs with hs | hs
      · exact (hi hs).elim
      · simp only [plus, decide_eq_false_iff_not] at hs
        omega
  · rfl

theorem node_eq_level_node {h i : ℕ} {v : VariablePosition h}
    (hv : depth v = i) : node v = TreePositions.node i v.2 := by
  simp [node, TreePositions.node, hv]

/-- Row plus child precedes row plus parent exactly for the stated parent-node inequality. -/
theorem row_plus_lt_iff {h i : ℕ} {child parent : VariablePosition h}
    (hc : AtLevel (i + 1) true child) (hp : AtLevel i true parent) :
    TreePositions.rowKey h child < TreePositions.rowKey h parent ↔
      node child / 2 ≤ node parent := by
  have hi : i < h := by have := hc.1 ▸ depth_le child; omega
  have hn₁ := node_eq_level_node hc.1
  have hn₂ := node_eq_level_node hp.1
  rw [hn₁, hn₂, eq_plusPos_of_atLevel hc, eq_plusPos_of_atLevel hp]
  exact TreePositions.row_plus_child_lt_parent hi child.2 parent.2

/-- Row minus parent precedes row minus child exactly for the parent-node inequality. -/
theorem row_minus_lt_iff {h i : ℕ} {child parent : VariablePosition h}
    (hc : AtLevel (i + 1) false child) (hp : AtLevel i false parent) :
    TreePositions.rowKey h parent < TreePositions.rowKey h child ↔
      node parent ≤ node child / 2 := by
  have hi : i < h := by have := hc.1 ▸ depth_le child; omega
  have hn₁ := node_eq_level_node hc.1
  have hn₂ := node_eq_level_node hp.1
  rw [hn₁, hn₂, eq_minusPos_of_atLevel hc, eq_minusPos_of_atLevel hp]
  exact TreePositions.row_minus_parent_lt_child hi child.2 parent.2

/-- Column plus parent precedes column plus child exactly for the parent-node inequality. -/
theorem column_plus_lt_iff {h i : ℕ} {child parent : VariablePosition h}
    (hc : AtLevel (i + 1) true child) (hp : AtLevel i true parent) :
    TreePositions.columnKey h parent < TreePositions.columnKey h child ↔
      node parent ≤ node child / 2 := by
  have hi : i < h := by have := hc.1 ▸ depth_le child; omega
  have hn₁ := node_eq_level_node hc.1
  have hn₂ := node_eq_level_node hp.1
  rw [hn₁, hn₂, eq_plusPos_of_atLevel hc, eq_plusPos_of_atLevel hp]
  exact TreePositions.column_plus_parent_lt_child hi child.2 parent.2

/-- Column minus child precedes column minus parent exactly for the parent-node inequality. -/
theorem column_minus_lt_iff {h i : ℕ} {child parent : VariablePosition h}
    (hc : AtLevel (i + 1) false child) (hp : AtLevel i false parent) :
    TreePositions.columnKey h child < TreePositions.columnKey h parent ↔
      node child / 2 ≤ node parent := by
  have hi : i < h := by have := hc.1 ▸ depth_le child; omega
  have hn₁ := node_eq_level_node hc.1
  have hn₂ := node_eq_level_node hp.1
  rw [hn₁, hn₂, eq_minusPos_of_atLevel hc, eq_minusPos_of_atLevel hp]
  exact TreePositions.column_minus_child_lt_parent hi child.2 parent.2

end Problem348.Construction

end OAI
