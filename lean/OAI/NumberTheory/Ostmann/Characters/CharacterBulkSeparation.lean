import OAI.NumberTheory.Ostmann.Characters.CharacterFullPrimeCells
import OAI.NumberTheory.Ostmann.Construction.ConstructedCharacterCells
import OAI.NumberTheory.Ostmann.Construction.SelectedAnchorDiagonalSplit

namespace OAI

/-! # The true bulk is disjoint from the complementary H cells -/
namespace Ostmann
open scoped Classical BigOperators

theorem selectedBulkLabel_disjoint_of_original {I : Type*}
    (role : I → CopyScheduleRole) (n m : ℕ) (bulk : Fin m ↪ I)
    (hbulk : ∀ i, role (bulk i) = .word) (Q : I → Finset ℕ)
    (hsep : ∀ i j, j ∉ Set.range bulk → role j ≠ .outside →
      Disjoint (Q (bulk i)) (Q j)) :
    ∀ a b : CopyScheduleH role n,
      selectedBulkLabel role n m bulk hbulk a ≠ selectedBulkLabel role n m bulk hbulk b →
      Disjoint (Q (copyScheduleOrigin n a.val)) (Q (copyScheduleOrigin n b.val)) := by
  have hside (a b : CopyScheduleH role n)
      (ha : a ∈ Set.range (selectedBulkH role n m bulk hbulk))
      (hb : b ∉ Set.range (selectedBulkH role n m bulk hbulk)) :
      Disjoint (Q (copyScheduleOrigin n a.val)) (Q (copyScheduleOrigin n b.val)) := by
    obtain ⟨x, rfl⟩ := ha
    have ho : copyScheduleOrigin n (selectedBulkH role n m bulk hbulk x).val = bulk x.2 :=
      copyScheduleOrigin_path n (scheduledPathEnumeration n x.1) (bulk x.2)
    rw [ho]
    apply hsep x.2 _ _ (copyScheduleH_origin_not_outside role n b)
    rintro ⟨i, hi⟩
    exact hb (mem_selectedBulkH_of_origin role n m bulk hbulk b i hi.symm)
  intro a b hab
  by_cases ha : a ∈ Set.range (selectedBulkH role n m bulk hbulk)
  · by_cases hb : b ∈ Set.range (selectedBulkH role n m bulk hbulk)
    · simp only [selectedBulkLabel, ha, hb, decide_true, ne_eq, not_true_eq_false] at hab
    · exact hside a b ha hb
  · by_cases hb : b ∈ Set.range (selectedBulkH role n m bulk hbulk)
    · exact (hside b a hb ha).symm
    · simp only [selectedBulkLabel, ha, hb, decide_false, ne_eq, not_true_eq_false] at hab

/-- The original top label is the only word slot outside the true bulk. No
separation between different anchor slots is assumed or needed. -/
theorem character_bulk_label_disjoint {k : ℕ} (m : ℕ) (r : Fin k → ℕ) (f n : ℕ)
    (Q : Fin (m + 1) → Finset ℕ) (U : Finset ℕ)
    (R : (v : CharacterCell k) → Fin (characterCellSize r f v) → Finset ℕ)
    (hQ : ∀ i : Fin m, Q i.succ = U) (htop : Disjoint U (Q 0))
    (hR : ∀ v i, Disjoint U (R v i)) :
    ∀ a b : CopyScheduleH (fun i : Σ v, Fin (characterSize m r f v) => characterRole k i.1) n,
      selectedBulkLabel _ n m (characterBulk m r f) (characterBulk_role m r f) a ≠
        selectedBulkLabel _ n m (characterBulk m r f) (characterBulk_role m r f) b →
      Disjoint (characterFullPrimeCells m r f Q R (copyScheduleOrigin n a.val))
        (characterFullPrimeCells m r f Q R (copyScheduleOrigin n b.val)) := by
  apply selectedBulkLabel_disjoint_of_original _ n m (characterBulk m r f)
    (characterBulk_role m r f) (characterFullPrimeCells m r f Q R)
  intro i j hj hout
  rw [characterFullPrimeCells_bulk, hQ]
  by_cases hw : characterRole k j.1 = .word
  · rw [character_word_not_bulk m r f j hw hj, characterFullPrimeCells_top]
    exact htop
  · rcases j with ⟨⟨b, v⟩, t⟩
    cases v with
    | none =>
      cases b with
      | false => exact False.elim (hout rfl)
      | true => exact False.elim (hw rfl)
    | some v => exact hR v t

theorem CharacterTargetWord.cell_loglog_lower {P : Finset ℕ} {F : ℕ → ℂ}
    {c δ U T : ℝ} {k : ℕ} (w : CharacterTargetWord P F c δ U k T)
    (h p : ℕ) (hp : p ∈ w.cell h) : U < Real.log (Real.log (p : ℝ)) := by
  have hh := (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2.1
  have hn : 0 ≤ (w.shell : ℝ) := Nat.cast_nonneg _
  linarith

theorem constructed_character_cells_bulk_disjoint {P : Finset ℕ} {F : ℕ → ℂ}
    {c δ U : ℝ} {k : ℕ} {T : Option (Fin k) → ℝ} {u : Fin k × Bool → ℝ}
    (w : ∀ j, CharacterTargetWord P F c δ U k (T j))
    (a : ∀ j, CharacterAnchorCell P F c δ (u j))
    (Q : Finset ℕ) (l h : ℝ)
    (hQ : ∀ p ∈ Q, l < Real.log (Real.log (p : ℝ)) ∧ Real.log (Real.log (p : ℝ)) ≤ h)
    (hU : h ≤ U) (hu : ∀ j, u j + 1 ≤ l ∨ h ≤ u j) :
    ∀ v i, Disjoint Q (characterPrimeCells w (characterAnchorCells a) v i) := by
  rintro (j | (j | v)) i
  · apply Finset.disjoint_left.mpr
    intro p hp hpc
    have hh := (w (some j)).cell_loglog_lower _ p hpc
    linarith [(hQ p hp).2]
  · apply Finset.disjoint_left.mpr
    intro p hp hpc
    have hh := (Finset.mem_filter.mp (Finset.mem_filter.mp hpc).1).2
    rcases hu j with hlow | hhigh
    · linarith [hh.2, (hQ p hp).1]
    · linarith [hh.1, (hQ p hp).2]
  · apply Finset.disjoint_left.mpr
    intro p hp hpc
    have hh := (w none).cell_loglog_lower _ p hpc
    linarith [(hQ p hp).2]

end Ostmann

end OAI
