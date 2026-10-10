import OAI.Combinatorics.MatrixRemoval.BodyExtension
import OAI.Combinatorics.MatrixRemoval.PathPropagation

namespace OAI

/-! Exact selected-anchor frames and their protected cells.
The frame does not constrain any of the four body entries. -/

noncomputable section
namespace Problem348.GuardedPath

structure AnchorFrame (n : ℕ) where
  rows : IncreasingMap 64 n
  cols : IncreasingMap 64 n

namespace AnchorFrame

variable {n : ℕ}

/-- All data needed to extend a body, except the body entries themselves. -/
structure Valid (F : AnchorFrame n) (A : BinaryMatrix n)
    (r₀ r₁ c₀ c₁ : Fin n) : Prop where
  row_before : ∀ u, F.rows.val u < r₀
  row_lt : r₀ < r₁
  col_before : ∀ v, F.cols.val v < c₀
  col_lt : c₀ < c₁
  anchor : ∀ u v, A (F.rows.val u) (F.cols.val v) = anchor64 u v
  row_zero : ∀ v, A r₀ (F.cols.val v) = decide (v.val = 0)
  row_one : ∀ v, A r₁ (F.cols.val v) = decide (v.val = 1)
  col_zero : ∀ u, A (F.rows.val u) c₀ = decide (u.val = 0)
  col_one : ∀ u, A (F.rows.val u) c₁ = decide (u.val = 1)

/-- Precisely the anchor and signature cells of one selected frame. -/
def Cell (F : AnchorFrame n) (r₀ r₁ c₀ c₁ : Fin n)
    (rc : Fin n × Fin n) : Prop :=
  (∃ u v, rc = (F.rows.val u, F.cols.val v)) ∨
  (∃ v, rc = (r₀, F.cols.val v) ∨ rc = (r₁, F.cols.val v)) ∨
  (∃ u, rc = (F.rows.val u, c₀) ∨ rc = (F.rows.val u, c₁))

/-- Agreement only on frame cells preserves anchor and signature validity. -/
theorem Valid.transfer {F : AnchorFrame n} {A B : BinaryMatrix n}
    {r₀ r₁ c₀ c₁ : Fin n} (hF : F.Valid A r₀ r₁ c₀ c₁)
    (hag : ∀ rc, F.Cell r₀ r₁ c₀ c₁ rc → A rc.1 rc.2 = B rc.1 rc.2) :
    F.Valid B r₀ r₁ c₀ c₁ := by
  refine ⟨hF.row_before, hF.row_lt, hF.col_before, hF.col_lt, ?_, ?_, ?_, ?_, ?_⟩
  · intro u v
    exact (hag _ (Or.inl ⟨u, v, rfl⟩)).symm.trans (hF.anchor u v)
  · intro v
    exact (hag _ (Or.inr (Or.inl ⟨v, Or.inl rfl⟩))).symm.trans (hF.row_zero v)
  · intro v
    exact (hag _ (Or.inr (Or.inl ⟨v, Or.inr rfl⟩))).symm.trans (hF.row_one v)
  · intro u
    exact (hag _ (Or.inr (Or.inr ⟨u, Or.inl rfl⟩))).symm.trans (hF.col_zero u)
  · intro u
    exact (hag _ (Or.inr (Or.inr ⟨u, Or.inr rfl⟩))).symm.trans (hF.col_one u)

/-- A valid frame and the body give a genuine ordered copy of the fixed H. -/
theorem Valid.not_HFree {F : AnchorFrame n} {B : BinaryMatrix n}
    {r₀ r₁ c₀ c₁ : Fin n} (hF : F.Valid B r₀ r₁ c₀ c₁)
    (hbody : PathPropagation.Body B r₀ r₁ c₀ c₁) : ¬ HFree fixedH B := by
  exact not_HFree_of_anchor_body B F.rows F.cols r₀ r₁ c₀ c₁
    hF.row_before hF.row_lt hF.col_before hF.col_lt
    hF.anchor hF.row_zero hF.row_one hF.col_zero hF.col_one
    hbody.1 hbody.2.1 hbody.2.2.1 hbody.2.2.2

end AnchorFrame
end Problem348.GuardedPath

end

end OAI
