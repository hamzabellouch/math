import OAI.Combinatorics.MatrixRemoval.AnchorPatternBridge
import OAI.Combinatorics.MatrixRemoval.AnchorProperties

namespace OAI

/-!
# Structural anchor bridges for the fixed pattern

The generic bridges are specialized to the explicit `anchor64` definition.
-/

universe uR uC

namespace Problem348.AnchorBridge

/-- The exact anchor realizes every five-bit word on the specified suffix. -/
theorem anchor64_word_block_complete (w : Fin 5 → Bool) :
    ∃ a : Fin 32, ∀ b : Fin 5,
      anchor64 (wordRow a) (wordCol b) = w b := by
  obtain ⟨a, ha⟩ := anchorWord_bijective.2 w
  refine ⟨a, fun b => ?_⟩
  have hb := congrFun ha b
  simpa only [anchorWord, wordRow, wordCol, Nat.add_comm] using hb

/-- An exact anchor copy has at least 33 anchors on one of its two axes,
provided anchors form prefixes and non-anchor rows do not shatter five
non-anchor columns. -/
theorem anchor64_anchor_majority {R : Type uR} {C : Type uC}
    (A : R → C → Bool) (row : Fin 64 → R) (col : Fin 64 → C)
    (anchorR : R → Prop) (anchorC : C → Prop)
    [DecidablePred anchorR] [DecidablePred anchorC]
    (hcopy : ∀ i j, A (row i) (col j) = anchor64 i j)
    (hcol : Function.Injective col)
    (hprefixR : ∀ i j, i ≤ j → anchorR (row j) → anchorR (row i))
    (hprefixC : ∀ i j, i ≤ j → anchorC (col j) → anchorC (col i))
    (hnoshatter : ∀ cs : Fin 5 → C, Function.Injective cs →
      (∀ b, ¬ anchorC (cs b)) → ∃ w : Fin 5 → Bool,
        ∀ r, ¬ anchorR r → ∃ b, A r (cs b) ≠ w b) :
    33 ≤ (Finset.univ.filter (fun i => anchorR (row i))).card ∨
    33 ≤ (Finset.univ.filter (fun j => anchorC (col j))).card := by
  rcases anchor_at_32_or_anchor_at_32 anchor64 A row col anchorR anchorC
    hcopy hcol hprefixR hprefixC anchor64_word_block_complete hnoshatter with hr | hc
  · exact Or.inl (prefix_card_lower_bound _ ⟨32, by decide⟩ hprefixR hr)
  · exact Or.inr (prefix_card_lower_bound _ ⟨32, by decide⟩ hprefixC hc)

/-- A row class of equal host rows occurs at most once in an anchor copy. -/
theorem anchor64_row_class_single_use {R : Type uR} {C : Type uC}
    (A : R → C → Bool) (row : Fin 64 → R) (col : Fin 64 → C)
    (P : R → Prop) [DecidablePred P]
    (hcopy : ∀ i j, A (row i) (col j) = anchor64 i j)
    (hclass : ∀ r s, P r → P s → A r = A s) :
    (Finset.univ.filter (fun i => P (row i))).card ≤ 1 :=
  card_selected_row_class_le_one anchor64 A row col P hcopy
    anchor64_rows_injective hclass

/-- A column class of equal host columns occurs at most once in an anchor copy. -/
theorem anchor64_col_class_single_use {R : Type uR} {C : Type uC}
    (A : R → C → Bool) (row : Fin 64 → R) (col : Fin 64 → C)
    (P : C → Prop) [DecidablePred P]
    (hcopy : ∀ i j, A (row i) (col j) = anchor64 i j)
    (hclass : ∀ c d, P c → P d → ∀ r, A r c = A r d) :
    (Finset.univ.filter (fun j => P (col j))).card ≤ 1 :=
  card_selected_col_class_le_one anchor64 A row col P hcopy
    anchor64_columns_injective hclass

end Problem348.AnchorBridge

end OAI
