import OAI.Combinatorics.MatrixRemoval.Host
import OAI.Combinatorics.MatrixRemoval.TreePositions
import OAI.Combinatorics.MatrixRemoval.AnchorFrames

namespace OAI

/-!
# The canonical host with both full-axis orders

The raw host, variable depth-first orders, and anchor/dummy order extension
give two orders. They are not global instances on the same carrier. Their
increasing enumerations are independent equivalences to the matrix size.
-/

noncomputable section

namespace Problem348.OrderedHost

open Construction

abbrev size (h : ℕ) := (386 * h + 2) * 2 ^ h

/-- Rows: anchors first, then the minus/subtree/plus tree order, then dummy. -/
abbrev rowOrder (h : ℕ) : LinearOrder (Position h) := by
  exact @AnchorFrames.rowOrder (Mode h) (VariablePosition h) (Fin (2 ^ h))
    inferInstance (TreePositions.positionOrder false h) inferInstance

/-- Columns: anchors first, then dummy, then the plus/subtree/minus tree order. -/
abbrev columnOrder (h : ℕ) : LinearOrder (Position h) := by
  exact @AnchorFrames.colOrder (Mode h) (VariablePosition h) (Fin (2 ^ h))
    inferInstance (TreePositions.positionOrder true h) inferInstance

/-- The increasing row enumeration, from raw positions to actual indices. -/
def rowIndex (h : ℕ) : Position h ≃ Fin (size h) := by
  letI := rowOrder h
  exact (monoEquivOfFin (Position h) (card_position h)).toEquiv.symm

/-- The increasing column enumeration, independent of the row enumeration. -/
def columnIndex (h : ℕ) : Position h ≃ Fin (size h) := by
  letI := columnOrder h
  exact (monoEquivOfFin (Position h) (card_position h)).toEquiv.symm

theorem rowIndex_lt_iff (h : ℕ) (r s : Position h) :
    rowIndex h r < rowIndex h s ↔ @LT.lt _ (rowOrder h).toLT r s := by
  let := rowOrder h
  exact @OrderIso.lt_iff_lt _ _ (rowOrder h).toPreorder inferInstance
    (@OrderIso.symm _ _ inferInstance (rowOrder h).toLE
      (monoEquivOfFin (Position h) (card_position h))) r s

theorem columnIndex_lt_iff (h : ℕ) (r s : Position h) :
    columnIndex h r < columnIndex h s ↔ @LT.lt _ (columnOrder h).toLT r s := by
  let := columnOrder h
  exact @OrderIso.lt_iff_lt _ _ (columnOrder h).toPreorder inferInstance
    (@OrderIso.symm _ _ inferInstance (columnOrder h).toLE
      (monoEquivOfFin (Position h) (card_position h))) r s

/-- On variable positions the full row enumeration has exactly the tree-key order. -/
theorem rowIndex_variable_lt_iff {h : ℕ} (v w : VariablePosition h) :
    rowIndex h (Sum.inr (Sum.inl v)) < rowIndex h (Sum.inr (Sum.inl w)) ↔
      TreePositions.rowKey h v < TreePositions.rowKey h w := by
  rw [rowIndex_lt_iff]
  exact @AnchorFrames.row_variable_lt_variable (Mode h) (VariablePosition h)
    (Fin (2 ^ h)) inferInstance (TreePositions.positionOrder false h) inferInstance v w

/-- On variable positions the full column enumeration has exactly the tree-key order. -/
theorem columnIndex_variable_lt_iff {h : ℕ} (v w : VariablePosition h) :
    columnIndex h (Sum.inr (Sum.inl v)) < columnIndex h (Sum.inr (Sum.inl w)) ↔
      TreePositions.columnKey h v < TreePositions.columnKey h w := by
  rw [columnIndex_lt_iff]
  exact @AnchorFrames.col_variable_lt_variable (Mode h) (VariablePosition h)
    (Fin (2 ^ h)) inferInstance (TreePositions.positionOrder true h) inferInstance v w

/-- Any representatives of the 64 successive anchor groups are increasing rows. -/
theorem row_anchor_strictMono {h : ℕ} (t : Mode h)
    (a : Fin 64 → Fin (2 ^ h)) :
    StrictMono (fun u => rowIndex h (Sum.inl (t, u, a u))) := by
  intro u v huv
  rw [rowIndex_lt_iff]
  exact @AnchorFrames.row_anchor_strictMono (Mode h) (VariablePosition h)
    (Fin (2 ^ h)) inferInstance (TreePositions.positionOrder false h) inferInstance
    t a u v huv

/-- The analogous anchor representatives are increasing columns. -/
theorem column_anchor_strictMono {h : ℕ} (t : Mode h)
    (a : Fin 64 → Fin (2 ^ h)) :
    StrictMono (fun u => columnIndex h (Sum.inl (t, u, a u))) := by
  intro u v huv
  rw [columnIndex_lt_iff]
  exact @AnchorFrames.col_anchor_strictMono (Mode h) (VariablePosition h)
    (Fin (2 ^ h)) inferInstance (TreePositions.positionOrder true h) inferInstance
    t a u v huv

theorem row_anchor_lt_nonanchor {h : ℕ} (t : Mode h) (u : Fin 64)
    (a : Fin (2 ^ h)) (x : VariablePosition h ⊕ Fin (2 ^ h)) :
    rowIndex h (Sum.inl (t, u, a)) < rowIndex h (Sum.inr x) := by
  rw [rowIndex_lt_iff]
  exact @AnchorFrames.row_anchor_lt_nonanchor (Mode h) (VariablePosition h)
    (Fin (2 ^ h)) inferInstance (TreePositions.positionOrder false h) inferInstance
    t u a x

theorem column_anchor_lt_nonanchor {h : ℕ} (t : Mode h) (u : Fin 64)
    (a : Fin (2 ^ h)) (x : VariablePosition h ⊕ Fin (2 ^ h)) :
    columnIndex h (Sum.inl (t, u, a)) < columnIndex h (Sum.inr x) := by
  rw [columnIndex_lt_iff]
  exact @AnchorFrames.col_anchor_lt_nonanchor (Mode h) (VariablePosition h)
    (Fin (2 ^ h)) inferInstance (TreePositions.positionOrder true h) inferInstance
    t u a x

theorem row_variable_lt_dummy {h : ℕ} (v : VariablePosition h) (x : Fin (2 ^ h)) :
    rowIndex h (Sum.inr (Sum.inl v)) < rowIndex h (Sum.inr (Sum.inr x)) := by
  rw [rowIndex_lt_iff]
  exact @AnchorFrames.row_variable_lt_dummy (Mode h) (VariablePosition h)
    (Fin (2 ^ h)) inferInstance (TreePositions.positionOrder false h) inferInstance v x

theorem column_dummy_lt_variable {h : ℕ} (v : VariablePosition h) (x : Fin (2 ^ h)) :
    columnIndex h (Sum.inr (Sum.inr x)) < columnIndex h (Sum.inr (Sum.inl v)) := by
  rw [columnIndex_lt_iff]
  exact @AnchorFrames.col_dummy_lt_variable (Mode h) (VariablePosition h)
    (Fin (2 ^ h)) inferInstance (TreePositions.positionOrder true h) inferInstance v x

/-- Initial-segment property for anchors, stated without an extra host predicate. -/
theorem row_anchor_initial {h : ℕ} {r s : Position h}
    (hrs : rowIndex h r < rowIndex h s) (hs : ∃ a, s = Sum.inl a) :
    ∃ a, r = Sum.inl a := by
  obtain ⟨⟨t, u, x⟩, rfl⟩ := hs
  rcases r with a | v
  · exact ⟨a, rfl⟩
  · exact False.elim (lt_asymm hrs (row_anchor_lt_nonanchor t u x v))

theorem column_anchor_initial {h : ℕ} {r s : Position h}
    (hrs : columnIndex h r < columnIndex h s) (hs : ∃ a, s = Sum.inl a) :
    ∃ a, r = Sum.inl a := by
  obtain ⟨⟨t, u, x⟩, rfl⟩ := hs
  rcases r with a | v
  · exact ⟨a, rfl⟩
  · exact False.elim (lt_asymm hrs (column_anchor_lt_nonanchor t u x v))

/-- First tree-order equivalence, now for the actual row indices. -/
theorem row_plus_child_lt_parent {h i : ℕ} (hi : i < h) (x y : Fin (2 ^ h)) :
    rowIndex h (.inr (.inl (TreePositions.plusPos (i + 1) (by omega) x))) <
      rowIndex h (.inr (.inl (TreePositions.plusPos i (by omega) y))) ↔
      TreePositions.node (i + 1) x / 2 ≤ TreePositions.node i y := by
  rw [rowIndex_variable_lt_iff]
  exact TreePositions.row_plus_child_lt_parent hi x y

/-- Second tree-order equivalence, now for the actual row indices. -/
theorem row_minus_parent_lt_child {h i : ℕ} (hi : i < h) (x y : Fin (2 ^ h)) :
    rowIndex h (.inr (.inl (TreePositions.minusPos i (by omega) y))) <
      rowIndex h (.inr (.inl (TreePositions.minusPos (i + 1) (by omega) x))) ↔
      TreePositions.node i y ≤ TreePositions.node (i + 1) x / 2 := by
  rw [rowIndex_variable_lt_iff]
  exact TreePositions.row_minus_parent_lt_child hi x y

/-- Third tree-order equivalence, now for the actual column indices. -/
theorem column_plus_parent_lt_child {h i : ℕ} (hi : i < h) (x y : Fin (2 ^ h)) :
    columnIndex h (.inr (.inl (TreePositions.plusPos i (by omega) y))) <
      columnIndex h (.inr (.inl (TreePositions.plusPos (i + 1) (by omega) x))) ↔
      TreePositions.node i y ≤ TreePositions.node (i + 1) x / 2 := by
  rw [columnIndex_variable_lt_iff]
  exact TreePositions.column_plus_parent_lt_child hi x y

/-- Fourth tree-order equivalence, now for the actual column indices. -/
theorem column_minus_child_lt_parent {h i : ℕ} (hi : i < h) (x y : Fin (2 ^ h)) :
    columnIndex h (.inr (.inl (TreePositions.minusPos (i + 1) (by omega) x))) <
      columnIndex h (.inr (.inl (TreePositions.minusPos i (by omega) y))) ↔
      TreePositions.node (i + 1) x / 2 ≤ TreePositions.node i y := by
  rw [columnIndex_variable_lt_iff]
  exact TreePositions.column_minus_child_lt_parent hi x y

end Problem348.OrderedHost

end

end OAI
