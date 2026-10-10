import OAI.NumberTheory.TwoPoint.Walks.TupleOccurrences
import OAI.NumberTheory.TwoPoint.Bounds.CenteredWordExpansion
import OAI.NumberTheory.TwoPoint.Bounds.MidpointCut
import OAI.NumberTheory.TwoPoint.Bounds.PerfectRows

namespace OAI

/-! The actual singleton and unlit slots determine the forest's perfect rows. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

noncomputable def perfectRows {ι : Type*} [Fintype ι] [DecidableEq ι] {R J : ℕ}
    (label : Fin R × Fin J → ι) (U : Finset (Fin R × Fin J)) : Finset (Fin R) :=
  ((singletonSlots label ∪ U).image Prod.fst)ᶜ

theorem perfectRows_lit {ι : Type*} [Fintype ι] [DecidableEq ι] {R J : ℕ}
    (label : Fin R × Fin J → ι) (U : Finset (Fin R × Fin J))
    (i : Fin R) (hi : i ∈ perfectRows label U) (j : Fin J) :
    (i, j) ∈ nonsingletonSlots label \ U := by
  have hnot : (i, j) ∉ singletonSlots label ∪ U := by
    intro h
    exact (mem_compl.mp hi) (mem_image.mpr ⟨(i, j), h, rfl⟩)
  have hs : label (i, j) ∉ singletonLabels label := by
    intro h
    exact hnot (mem_union_left _ (mem_filter.mpr ⟨mem_univ _, h⟩))
  have hp : 0 < (labelOccurrences label (label (i, j))).card :=
    card_pos.mpr ⟨(i, j), mem_filter.mpr ⟨mem_univ _, rfl⟩⟩
  refine mem_sdiff.mpr ⟨mem_filter.mpr ⟨mem_univ _, ?_⟩, ?_⟩
  · simp only [singletonLabels, nonsingletonLabels, mem_filter, mem_univ, true_and] at hs ⊢
    omega
  · exact fun hu => hnot (mem_union_right _ hu)

theorem perfectRows_imperfect_le {ι : Type*} [Fintype ι] [DecidableEq ι] {R J : ℕ}
    (label : Fin R × Fin J → ι) (U : Finset (Fin R × Fin J)) (cut : Fin R) :
    imperfectColumnCount ((perfectRows label U).erase cut) ≤
      (singletonLabels label).card + U.card + 1 := by
  apply (imperfectColumnCount_erase_le _ _).trans
  apply Nat.add_le_add_right
  rw [imperfectColumnCount_eq_card_compl, perfectRows, compl_compl]
  exact (card_image_le.trans (card_union_le _ _)).trans_eq
    (congrArg (· + U.card) (singleton_slot_count label))

theorem tuple_perfectRows_imperfect_le {J R : ℕ} {P : Fin J → Finset ℕ}
    (w : ColumnPrimeAssignment J R P) (U : Finset (Fin R × Fin J)) (cut : Fin R) :
    imperfectColumnCount ((perfectRows (tupleSlotLabel w) U).erase cut) ≤
      columnSingletonCount w + U.card + 1 := by
  simpa only [tupleSlotLabel_singletons] using
    perfectRows_imperfect_le (tupleSlotLabel w) U cut

theorem eventually_tuple_perfectRows_budget :
    ∀ᶠ L : ℝ in Filter.atTop, ∀ (J R : ℕ) (P : Fin J → Finset ℕ)
      (w : ColumnPrimeAssignment J R P) (U : Finset (Fin R × Fin J)) (cut : Fin R),
      (columnSingletonCount w : ℝ) ≤ L ^ (1 / 4 : ℝ) →
      (U.card : ℝ) ≤ L ^ (1 / 50 : ℝ) →
      (imperfectColumnCount ((perfectRows (tupleSlotLabel w) U).erase cut) : ℝ) ≤
        2 * L ^ (1 / 4 : ℝ) := by
  filter_upwards [eventually_imperfect_with_cut_bound] with L hL
  intro J R P w U cut hS hU
  exact hL _ _ _ (tuple_perfectRows_imperfect_le w U cut) hS hU

end TwoPointCorrelations

end OAI
