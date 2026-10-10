import OAI.Probability.ThorpShuffle.FirstMoment

namespace OAI

noncomputable section

namespace Thorp.Current
open scoped BigOperators Classical
open Thorp.Specht Thorp.Young

/-- Verification that the index predicate in `exceptionalFirst` excludes exactly
the row and the column, rather than a merely degree-based surrogate. -/
lemma full_row_iff (D : YoungDiagram) :
    D.rowLen 0 = Fintype.card (Cells D) ↔ ∀ x : Cells D, x.val.1 = 0 := by
  constructor
  · intro h
    have hc : Fintype.card (Lower D) = 0 := by have hh := card_lower_add D; omega
    have he : IsEmpty (Lower D) := Fintype.card_eq_zero_iff.mp hc
    intro x
    by_contra hx
    exact he.false ⟨x, hx⟩
  · intro h
    have he : IsEmpty (Lower D) := ⟨fun x => x.property (h x.val)⟩
    have hc : Fintype.card (Lower D) = 0 := Fintype.card_eq_zero_iff.mpr he
    have hh := card_lower_add D
    omega

lemma full_column_iff (D : YoungDiagram) :
    D.colLen 0 = Fintype.card (Cells D) ↔ ∀ x : Cells D, x.val.2 = 0 := by
  have hc := Fintype.card_congr (transposeCells D).toEquiv
  constructor
  · intro h x
    have hT : D.transpose.rowLen 0 = Fintype.card (Cells D.transpose) := by
      rw [YoungDiagram.rowLen_transpose, ← hc, h]
    exact (full_row_iff D.transpose).mp hT (transposeCells D x)
  · intro h
    have hT : D.transpose.rowLen 0 = Fintype.card (Cells D.transpose) :=
      (full_row_iff D.transpose).mpr (fun x => h ((transposeCells D).symm x))
    simpa only [YoungDiagram.rowLen_transpose, ← hc] using hT

lemma defect_zero_iff_row_or_column {n : ℕ} (p : NShape n) :
    defect p = 0 ↔
      (∀ x : Cells (ofPartition p), x.val.1 = 0) ∨
      (∀ x : Cells (ofPartition p), x.val.2 = 0) := by
  rw [← full_row_iff, ← full_column_iff, diagram_card]
  have hd := defect_add_longest p
  have hL := longest_le_card (ofPartition p)
  rw [diagram_card] at hL
  unfold longest at hd hL
  omega

lemma exceptionalFirst_exact_nonrow_noncolumn (n : ℕ) :
    exceptionalFirst n = ∑ p : NShape n,
      if (¬∀ x : Cells (ofPartition p), x.val.1 = 0) ∧
         (¬∀ x : Cells (ofPartition p), x.val.2 = 0)
      then (degree p : ℝ)⁻¹ else 0 := by
  unfold exceptionalFirst
  apply Finset.sum_congr rfl
  intro p _
  have h : 0 < defect p ↔
      (¬∀ x : Cells (ofPartition p), x.val.1 = 0) ∧
      (¬∀ x : Cells (ofPartition p), x.val.2 = 0) := by
    rw [Nat.pos_iff_ne_zero, ne_eq, defect_zero_iff_row_or_column, not_or]
  simp only [h]

end Thorp.Current

end

end OAI
