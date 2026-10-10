import OAI.Combinatorics.BinaryEdit.Model
import OAI.Combinatorics.TreeEdit.EditMetric
import Mathlib

namespace OAI

/-! Longest common subsequence bounds for rows over disjoint tagged alphabets. -/
namespace TreeEdit.BinaryLower.TaggedRow
open scoped BigOperators

/-- Concatenation in increasing block-index order. -/
def row {α : Type*} {m : ℕ} (blocks : Fin m → List α) : List α :=
  (List.finRange m).flatMap blocks

theorem row_eq_flatten_ofFn {α : Type*} {m : ℕ} (X : Fin m → List α) :
    row X = (List.ofFn X).flatten := by
  simp [row, List.flatMap, List.finRange, List.map_ofFn, Function.comp_def]

private theorem flatMap_single_index {I α : Type*} [DecidableEq I]
    (order : List I) (hn : order.Nodup) (i : I) (f : I → List α) :
    order.flatMap (fun j => if j = i then f j else []) =
      if i ∈ order then f i else [] := by
  induction order with
  | nil => simp
  | cons j order ih =>
    obtain ⟨hj, htail⟩ := List.nodup_cons.mp hn
    by_cases hji : j = i
    · subst j
      rw [List.flatMap_cons, ite_eq_left rfl, ih htail]
      simp [hj]
    · rw [List.flatMap_cons, ite_eq_right hji, List.nil_append, ih htail]
      simp only [List.mem_cons, Ne.symm hji, false_or]

theorem filter_row {α : Type*} {m : ℕ} (tag : α → Fin m)
    (blocks : Fin m → List α)
    (htags : ∀ j, ∀ a ∈ blocks j, tag a = j) (i : Fin m) :
    (row blocks).filter (fun a => decide (tag a = i)) = blocks i := by
  rw [row, List.filter_flatMap]
  have hb : ∀ j, (blocks j).filter (fun a => decide (tag a = i)) =
      if j = i then blocks j else [] := by
    intro j
    by_cases hji : j = i
    · subst j
      rw [ite_eq_left rfl]
      apply List.filter_eq_self.mpr
      intro a ha
      simp [htags i a ha]
    · simp only [ite_eq_right hji]
      apply List.filter_eq_nil_iff.mpr
      intro a ha
      simp [htags j a ha, hji]
  rw [List.flatMap_congr (fun j _ => hb j)]
  rw [flatMap_single_index _ (List.nodup_finRange m)]
  simp

/-- Tag fibers partition every finite word's positions. -/
theorem sum_length_filter_tag {α I : Type*} [Fintype I] [DecidableEq I]
    (tag : α → I) (z : List α) :
    (∑ i, (z.filter (fun a => decide (tag a = i))).length) = z.length := by
  induction z with
  | nil => simp
  | cons a z ih =>
    have heq : ∀ i, ((a :: z).filter (fun b => decide (tag b = i))).length =
        (if tag a = i then 1 else 0) +
          (z.filter (fun b => decide (tag b = i))).length := by
      intro i
      by_cases h : tag a = i <;> simp [h, Nat.add_comm]
    simp_rw [heq]
    rw [Finset.sum_add_distrib, ih]
    simp [Nat.add_comm]

/-- Common subsequences of rows are bounded by the sum of block LCS lengths. -/
theorem common_sublist_length_le_sum_lcs {α : Type*} {m : ℕ}
    (tag : α → Fin m) (X Y : Fin m → List α)
    (hX : ∀ i, ∀ a ∈ X i, tag a = i)
    (hY : ∀ i, ∀ a ∈ Y i, tag a = i)
    {z : List α} (hzX : z.Sublist (row X)) (hzY : z.Sublist (row Y)) :
    z.length ≤ ∑ i, lcs (X i) (Y i) := by
  rw [← sum_length_filter_tag tag z]
  apply Finset.sum_le_sum
  intro i _
  have hx := hzX.filter (fun a => decide (tag a = i))
  have hy := hzY.filter (fun a => decide (tag a = i))
  rw [filter_row tag X hX i] at hx
  rw [filter_row tag Y hY i] at hy
  exact length_le_lcs hx hy

/-- Local row bound used in the nonsplit-row argument. -/
theorem lcs_row_le_sum {α : Type*} {m : ℕ}
    (tag : α → Fin m) (X Y : Fin m → List α)
    (hX : ∀ i, ∀ a ∈ X i, tag a = i)
    (hY : ∀ i, ∀ a ∈ Y i, tag a = i) :
    lcs (row X) (row Y) ≤ ∑ i, lcs (X i) (Y i) := by
  apply csSup_le
  · exact ⟨0, [], by simp, by simp, rfl⟩
  · intro n hn
    obtain ⟨z, hzX, hzY, rfl⟩ := hn
    exact common_sublist_length_le_sum_lcs tag X Y hX hY hzX hzY

/-- Exact length of an equal-block row. -/
theorem length_row {α : Type*} {m B : ℕ} (X : Fin m → List α)
    (hX : ∀ i, (X i).length = B) : (row X).length = m * B := by
  simp [row, List.length_flatMap, hX]

/-- Tagwise deficits accumulate in a single pair of rows. This is the
local deficit estimate consumed by the nonsplit-row counting argument. -/
theorem sum_deficit_le_row_deficit {α : Type*} {m B : ℕ}
    (tag : α → Fin m) (X Y : Fin m → List α)
    (hX : ∀ i, ∀ a ∈ X i, tag a = i)
    (hY : ∀ i, ∀ a ∈ Y i, tag a = i)
    (hXL : ∀ i, (X i).length = B) :
    (∑ i, deficit B (X i) (Y i)) ≤ deficit (m * B) (row X) (row Y) := by
  have hsplit : (∑ i, deficit B (X i) (Y i)) +
      (∑ i, lcs (X i) (Y i)) = m * B := by
    rw [← Finset.sum_add_distrib]
    have heq : ∀ i, deficit B (X i) (Y i) + lcs (X i) (Y i) = B := by
      intro i
      apply Nat.sub_add_cancel
      simpa [hXL i] using lcs_le_length_left (X i) (Y i)
    simp_rw [heq]
    simp
  have hlocal := lcs_row_le_sum tag X Y hX hY
  exact Nat.le_sub_of_add_le
    ((Nat.add_le_add_left hlocal _).trans_eq hsplit)

/-- Real-valued LCS row capacity, convenient when a separate matching
restriction lemma has already bounded a row-pair count by its LCS. -/
theorem lcs_row_le_capacity_sub {α : Type*} {m B : ℕ}
    (tag : α → Fin m) (X Y : Fin m → List α)
    (hX : ∀ i, ∀ a ∈ X i, tag a = i)
    (hY : ∀ i, ∀ a ∈ Y i, tag a = i)
    (hXL : ∀ i, (X i).length = B)
    {d : ℝ} (hd : d ≤ ∑ i, (deficit B (X i) (Y i) : ℝ)) :
    (lcs (row X) (row Y) : ℝ) ≤ (m : ℝ) * B - d := by
  have hdef := sum_deficit_le_row_deficit tag X Y hX hY hXL
  have hlen : lcs (row X) (row Y) ≤ m * B := by
    simpa [length_row X hXL] using lcs_le_length_left (row X) (row Y)
  have hnat : (∑ i, deficit B (X i) (Y i)) + lcs (row X) (row Y) ≤ m * B := by
    change (∑ i, deficit B (X i) (Y i)) ≤ m * B - lcs (row X) (row Y) at hdef
    omega
  have hreal : (∑ i, (deficit B (X i) (Y i) : ℝ)) +
      (lcs (row X) (row Y) : ℝ) ≤ (m : ℝ) * B := by
    exact_mod_cast hnat
  linarith

/-- Real-valued version matching the manuscript's local row-loss hypothesis. -/
theorem common_sublist_length_le_capacity_sub {α : Type*} {m B : ℕ}
    (tag : α → Fin m) (X Y : Fin m → List α)
    (hX : ∀ i, ∀ a ∈ X i, tag a = i)
    (hY : ∀ i, ∀ a ∈ Y i, tag a = i)
    (hXL : ∀ i, (X i).length = B)
    {d : ℝ} (hd : d ≤ ∑ i, (deficit B (X i) (Y i) : ℝ))
    {z : List α} (hzX : z.Sublist (row X)) (hzY : z.Sublist (row Y)) :
    (z.length : ℝ) ≤ (m : ℝ) * B - d := by
  have hn := common_sublist_length_le_sum_lcs tag X Y hX hY hzX hzY
  have heq : (∑ i, deficit B (X i) (Y i)) +
      (∑ i, lcs (X i) (Y i)) = m * B := by
    rw [← Finset.sum_add_distrib]
    have hsplit : ∀ i, deficit B (X i) (Y i) + lcs (X i) (Y i) = B := by
      intro i
      apply Nat.sub_add_cancel
      simpa [hXL i] using lcs_le_length_left (X i) (Y i)
    simp_rw [hsplit]
    simp
  have hsum : (∑ i, (deficit B (X i) (Y i) : ℝ)) +
      (∑ i, (lcs (X i) (Y i) : ℝ)) = (m : ℝ) * B := by
    exact_mod_cast heq
  have hnreal : (z.length : ℝ) ≤ ∑ i, (lcs (X i) (Y i) : ℝ) := by
    exact_mod_cast hn
  linarith

/-- Pairwise disjoint alphabets admit a tag on the ambient alphabet. Values
outside their union are irrelevant and receive an arbitrary default tag. -/
theorem exists_tag_of_pairwise_disjoint {α I : Type*} [Nonempty I]
    (Γ : I → Set α) (hΓ : Pairwise fun i j => Disjoint (Γ i) (Γ j)) :
    ∃ tag : α → I, ∀ i, ∀ a ∈ Γ i, tag a = i := by
  classical
  let tag : α → I := fun a =>
    if h : ∃ i, a ∈ Γ i then h.choose else Classical.arbitrary I
  refine ⟨tag, ?_⟩
  intro i a ha
  dsimp [tag]
  split_ifs with h
  · by_contra hne
    exact Set.disjoint_left.mp (hΓ hne) h.choose_spec ha
  · exact False.elim (h ⟨i, ha⟩)

/-- The row LCS bound stated directly for the manuscript's pairwise disjoint
alphabets, without asking the caller to provide a tag function. -/
theorem lcs_row_le_sum_of_disjoint {α : Type*} {m : ℕ} (hm : 0 < m)
    (Γ : Fin m → Set α)
    (hΓ : Pairwise fun i j => Disjoint (Γ i) (Γ j))
    (X Y : Fin m → List α)
    (hX : ∀ i, ∀ a ∈ X i, a ∈ Γ i)
    (hY : ∀ i, ∀ a ∈ Y i, a ∈ Γ i) :
    lcs (row X) (row Y) ≤ ∑ i, lcs (X i) (Y i) := by
  have : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  obtain ⟨tag, htag⟩ := exists_tag_of_pairwise_disjoint Γ hΓ
  apply lcs_row_le_sum tag X Y
  · intro i a ha
    exact htag i a (hX i a ha)
  · intro i a ha
    exact htag i a (hY i a ha)

end TreeEdit.BinaryLower.TaggedRow

end OAI
