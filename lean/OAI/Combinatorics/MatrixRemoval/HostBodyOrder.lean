import OAI.Combinatorics.MatrixRemoval.HostBodyModes
import OAI.Combinatorics.MatrixRemoval.HostTreeOrder

namespace OAI

/-!
# From increasing body positions to the four node-order inequalities

These lemmas use the actual host roles and tree keys. Each independent
coordinate map reflects the corresponding tree-key order on variable
positions; no mode-specific ordering is assumed.
-/

universe uAlpha uR uC

namespace Problem348.Construction

theorem vertical_plus_node_order {h : ℕ} {α : Type uAlpha} [Preorder α]
    (rowIndex : Position h → α)
    (hkey : ∀ v w : VariablePosition h,
      rowIndex (Sum.inr (Sum.inl v)) < rowIndex (Sum.inr (Sum.inl w)) →
        TreePositions.rowKey h v < TreePositions.rowKey h w)
    {t : Mode h} (hk : kind t = 0) {r₀ r₁ : Position h}
    (hr₀ : rowRole t 0 r₀) (hr₁ : rowRole t 1 r₁)
    (hrow : rowIndex r₀ < rowIndex r₁) :
    positionNode r₀ / 2 ≤ positionNode r₁ := by
  have hkt : kind t < 2 := by omega
  obtain ⟨x, rfl⟩ := rowRole_vertical_variable hkt hr₀
  obtain ⟨y, rfl⟩ := rowRole_vertical_variable hkt hr₁
  have hx : AtLevel (level t) true x := by simpa [rowRole, hk] using hr₀
  have hy : AtLevel (level t - 1) true y := by simpa [rowRole, hk] using hr₁
  have hl : level t - 1 + 1 = level t := by have := level_pos t; omega
  exact (row_plus_lt_iff (hl ▸ hx) hy).mp (hkey x y hrow)

theorem vertical_minus_node_order {h : ℕ} {α : Type uAlpha} [Preorder α]
    (rowIndex : Position h → α)
    (hkey : ∀ v w : VariablePosition h,
      rowIndex (Sum.inr (Sum.inl v)) < rowIndex (Sum.inr (Sum.inl w)) →
        TreePositions.rowKey h v < TreePositions.rowKey h w)
    {t : Mode h} (hk : kind t = 1) {r₀ r₁ : Position h}
    (hr₀ : rowRole t 0 r₀) (hr₁ : rowRole t 1 r₁)
    (hrow : rowIndex r₀ < rowIndex r₁) :
    positionNode r₀ ≤ positionNode r₁ / 2 := by
  have hkt : kind t < 2 := by omega
  obtain ⟨x, rfl⟩ := rowRole_vertical_variable hkt hr₀
  obtain ⟨y, rfl⟩ := rowRole_vertical_variable hkt hr₁
  have hx : AtLevel (level t - 1) false x := by simpa [rowRole, hk] using hr₀
  have hy : AtLevel (level t) false y := by simpa [rowRole, hk] using hr₁
  have hl : level t - 1 + 1 = level t := by have := level_pos t; omega
  exact (row_minus_lt_iff (hl ▸ hy) hx).mp (hkey x y hrow)

theorem horizontal_plus_node_order {h : ℕ} {α : Type uAlpha} [Preorder α]
    (colIndex : Position h → α)
    (hkey : ∀ v w : VariablePosition h,
      colIndex (Sum.inr (Sum.inl v)) < colIndex (Sum.inr (Sum.inl w)) →
        TreePositions.columnKey h v < TreePositions.columnKey h w)
    {t : Mode h} (hklo : 2 ≤ kind t) (hkhi : kind t < 4)
    {c₀ c₁ : Position h} (hc₀ : colRole t 0 c₀) (hc₁ : colRole t 1 c₁)
    (hcol : colIndex c₀ < colIndex c₁) :
    positionNode c₀ ≤ positionNode c₁ / 2 := by
  obtain ⟨x, rfl⟩ := colRole_horizontal_variable hklo hc₀
  obtain ⟨y, rfl⟩ := colRole_horizontal_variable hklo hc₁
  have hkn : ¬ kind t < 2 := by omega
  have hx : AtLevel (level t - 1) true x := by
    simpa [colRole, hkn, hkhi] using hc₀
  have hy : AtLevel (level t) true y := by
    have hy' : AtLevel (level t) true y ∧ node y % 2 = kind t % 2 := by
      simpa [colRole, hkn, hkhi] using hc₁
    exact hy'.1
  have hl : level t - 1 + 1 = level t := by have := level_pos t; omega
  exact (column_plus_lt_iff (hl ▸ hy) hx).mp (hkey x y hcol)

theorem horizontal_minus_node_order {h : ℕ} {α : Type uAlpha} [Preorder α]
    (colIndex : Position h → α)
    (hkey : ∀ v w : VariablePosition h,
      colIndex (Sum.inr (Sum.inl v)) < colIndex (Sum.inr (Sum.inl w)) →
        TreePositions.columnKey h v < TreePositions.columnKey h w)
    {t : Mode h} (hk : 4 ≤ kind t)
    {c₀ c₁ : Position h} (hc₀ : colRole t 0 c₀) (hc₁ : colRole t 1 c₁)
    (hcol : colIndex c₀ < colIndex c₁) :
    positionNode c₀ / 2 ≤ positionNode c₁ := by
  have hklo : 2 ≤ kind t := by omega
  obtain ⟨x, rfl⟩ := colRole_horizontal_variable hklo hc₀
  obtain ⟨y, rfl⟩ := colRole_horizontal_variable hklo hc₁
  have hkn : ¬ kind t < 2 := by omega
  have hkhi : ¬ kind t < 4 := by omega
  have hx : AtLevel (level t) false x := by
    have hx' : AtLevel (level t) false x ∧ node x % 2 = kind t % 2 := by
      simpa [colRole, hkn, hkhi] using hc₀
    exact hx'.1
  have hy : AtLevel (level t - 1) false y := by
    simpa [colRole, hkn, hkhi] using hc₁
  have hl : level t - 1 + 1 = level t := by have := level_pos t; omega
  exact (column_minus_lt_iff (hl ▸ hx) hy).mp (hkey x y hcol)

/-- Increasing positions in the actual two tree orders satisfy precisely the
node-order premise of the exhaustive six-mode localization theorem. -/
theorem bodyNodeOrder_of_ordered {h : ℕ} {R : Type uR} {C : Type uC} [Preorder R] [Preorder C]
    (rowIndex : Position h → R) (colIndex : Position h → C)
    (hrowKey : ∀ v w : VariablePosition h,
      rowIndex (Sum.inr (Sum.inl v)) < rowIndex (Sum.inr (Sum.inl w)) →
        TreePositions.rowKey h v < TreePositions.rowKey h w)
    (hcolKey : ∀ v w : VariablePosition h,
      colIndex (Sum.inr (Sum.inl v)) < colIndex (Sum.inr (Sum.inl w)) →
        TreePositions.columnKey h v < TreePositions.columnKey h w)
    {t : Mode h} {r₀ r₁ c₀ c₁ : Position h}
    (hr₀ : rowRole t 0 r₀) (hr₁ : rowRole t 1 r₁)
    (hc₀ : colRole t 0 c₀) (hc₁ : colRole t 1 c₁)
    (hrow : rowIndex r₀ < rowIndex r₁) (hcol : colIndex c₀ < colIndex c₁) :
    BodyNodeOrder t r₀ r₁ c₀ c₁ := by
  unfold BodyNodeOrder
  split_ifs with hk₀ hk₁ hk₄
  · exact vertical_plus_node_order rowIndex hrowKey hk₀ hr₀ hr₁ hrow
  · exact vertical_minus_node_order rowIndex hrowKey hk₁ hr₀ hr₁ hrow
  · exact horizontal_plus_node_order colIndex hcolKey (by omega) hk₄ hc₀ hc₁ hcol
  · exact horizontal_minus_node_order colIndex hcolKey (by omega) hc₀ hc₁ hcol

/-- The concrete host localization conclusion, with the numerical mode-order
certificate discharged by the constructed key orders and increasing coordinates. -/
theorem host_ordered_body_leaf_diagonal {h : ℕ} {R : Type uR} {C : Type uC}
    [Preorder R] [Preorder C]
    (rowIndex : Position h → R) (colIndex : Position h → C)
    (hrowKey : ∀ v w : VariablePosition h,
      rowIndex (Sum.inr (Sum.inl v)) < rowIndex (Sum.inr (Sum.inl w)) →
        TreePositions.rowKey h v < TreePositions.rowKey h w)
    (hcolKey : ∀ v w : VariablePosition h,
      colIndex (Sum.inr (Sum.inl v)) < colIndex (Sum.inr (Sum.inl w)) →
        TreePositions.columnKey h v < TreePositions.columnKey h w)
    {t : Mode h} {r₀ r₁ c₀ c₁ : Position h}
    (hr₀ : rowRole t 0 r₀) (hr₁ : rowRole t 1 r₁)
    (hc₀ : colRole t 0 c₀) (hc₁ : colRole t 1 c₁)
    (hrow : rowIndex r₀ < rowIndex r₁) (hcol : colIndex c₀ < colIndex c₁)
    (hb : ModeLocalization.IsP (host r₀ c₀) (host r₀ c₁)
      (host r₁ c₀) (host r₁ c₁)) :
    ∃ z : Fin (2 ^ h),
      r₀ = Sum.inr (Sum.inl (Fin.last (2 * h), z)) ∧
      c₀ = Sum.inr (Sum.inl (Fin.last (2 * h), z)) := by
  exact host_body_leaf_diagonal hr₀ hr₁ hc₀ hc₁
    (bodyNodeOrder_of_ordered rowIndex colIndex hrowKey hcolKey hr₀ hr₁ hc₀ hc₁ hrow hcol) hb

end Problem348.Construction

end OAI
