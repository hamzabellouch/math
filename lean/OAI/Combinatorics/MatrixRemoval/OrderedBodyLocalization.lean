import OAI.Combinatorics.MatrixRemoval.OrderedHost
import OAI.Combinatorics.MatrixRemoval.HostBodyOrder

namespace OAI

/-!
# Body localization for the independent host enumerations

The canonical full-axis enumeration gives exhaustive body-mode localization.
All comparisons use the actual row and column indices; no order-reflection
certificate remains as an assumption.
-/

namespace Problem348.OrderedHost

open Construction

theorem rowIndex_reflects_variable_order {h : ℕ} (v w : VariablePosition h)
    (hvw : rowIndex h (.inr (.inl v)) < rowIndex h (.inr (.inl w))) :
    TreePositions.rowKey h v < TreePositions.rowKey h w :=
  (rowIndex_variable_lt_iff v w).mp hvw

theorem columnIndex_reflects_variable_order {h : ℕ} (v w : VariablePosition h)
    (hvw : columnIndex h (.inr (.inl v)) < columnIndex h (.inr (.inl w))) :
    TreePositions.columnKey h v < TreePositions.columnKey h w :=
  (columnIndex_variable_lt_iff v w).mp hvw

/-- The actual independent enumerations discharge all four numerical mode orders. -/
theorem bodyNodeOrder_of_indices {h : ℕ} {t : Mode h}
    {r₀ r₁ c₀ c₁ : Position h}
    (hr₀ : rowRole t 0 r₀) (hr₁ : rowRole t 1 r₁)
    (hc₀ : colRole t 0 c₀) (hc₁ : colRole t 1 c₁)
    (hrow : rowIndex h r₀ < rowIndex h r₁)
    (hcol : columnIndex h c₀ < columnIndex h c₁) :
    BodyNodeOrder t r₀ r₁ c₀ c₁ :=
  bodyNodeOrder_of_ordered (rowIndex h) (columnIndex h)
    rowIndex_reflects_variable_order columnIndex_reflects_variable_order
    hr₀ hr₁ hc₀ hc₁ hrow hcol

/-- Every correctly assigned ordered body in the canonical host has its
top-left cell on the shared leaf diagonal. -/
theorem body_leaf_diagonal {h : ℕ} {t : Mode h}
    {r₀ r₁ c₀ c₁ : Position h}
    (hr₀ : rowRole t 0 r₀) (hr₁ : rowRole t 1 r₁)
    (hc₀ : colRole t 0 c₀) (hc₁ : colRole t 1 c₁)
    (hrow : rowIndex h r₀ < rowIndex h r₁)
    (hcol : columnIndex h c₀ < columnIndex h c₁)
    (hb : ModeLocalization.IsP (host r₀ c₀) (host r₀ c₁)
      (host r₁ c₀) (host r₁ c₁)) :
    ∃ z : Fin (2 ^ h),
      r₀ = Sum.inr (Sum.inl (Fin.last (2 * h), z)) ∧
      c₀ = Sum.inr (Sum.inl (Fin.last (2 * h), z)) :=
  host_ordered_body_leaf_diagonal (rowIndex h) (columnIndex h)
    rowIndex_reflects_variable_order columnIndex_reflects_variable_order
    hr₀ hr₁ hc₀ hc₁ hrow hcol hb

end Problem348.OrderedHost

end OAI
