import OAI.Combinatorics.ExpectationThreshold.SelectorDefinitions

namespace OAI

/-!
# Exact counts in a selector profile

The full profile records each strict downward move by its final and original
colors. These counting identities hold even without a global `Earlier`
hypothesis: every point counted by a crossing already moves downward.
-/

noncomputable section

open scoped BigOperators

namespace TalagrandThreshold.Selector

variable {α : Type*} [Fintype α] [DecidableEq α] {s : ℕ}

omit [DecidableEq α] in
/-- A profile entry is the original-color fiber within its moved row. -/
theorem profile_eq_card_filter_movedRow (a z : Coloring α s)
    (i : Fin s) (h : Color s) :
    profile a z i h = ((movedRow a z i).filter fun x => a x = h).card := by
  unfold profile movedRow
  congr 1
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨hz, ha, hi⟩
    exact ⟨⟨hz, by simpa only [hz, ha] using hi⟩, ha⟩
  · rintro ⟨⟨hz, hi⟩, ha⟩
    exact ⟨hz, ha, by simpa only [hz, ha] using hi⟩

omit [DecidableEq α] in
/-- All original colors partition the moved row. -/
theorem rowCount_profile (a z : Coloring α s) (i : Fin s) :
    rowCount (profile a z) i = (movedRow a z i).card := by
  unfold rowCount
  simp_rw [profile_eq_card_filter_movedRow]
  simpa using Finset.sum_card_fiberwise_eq_card_filter
    (movedRow a z i) Finset.univ a

omit [DecidableEq α] in
theorem movedRow_card_eq_rowCount (a z : Coloring α s) (i : Fin s) :
    (movedRow a z i).card = rowCount (profile a z) i :=
  (rowCount_profile a z i).symm

omit [DecidableEq α] in
theorem movedRow_subset_changes (a z : Coloring α s) (i : Fin s) :
    movedRow a z i ⊆ changes a z := by
  intro x hx
  have hx' : (z x).val = i.val ∧ (z x).val < (a x).val := by
    simpa only [movedRow, Finset.mem_filter, Finset.mem_univ, true_and] using hx
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ x, hx'.2⟩

omit [DecidableEq α] in
/-- The last color cannot be the final color of a strict downward move. -/
theorem changes_filter_last (a z : Coloring α s) :
    (changes a z).filter (fun x => z x = Fin.last s) = ∅ := by
  ext x
  simp only [Finset.mem_filter, changes, Finset.mem_univ, true_and,
    Finset.notMem_empty, iff_false, not_and]
  intro hmove hlast
  have hlt : (z x).val < (a x).val := hmove
  have hz : (z x).val = s := congrArg Fin.val hlast
  have ha := (a x).isLt
  omega

omit [DecidableEq α] in
/-- The nonterminal final-color fibers are exactly the moved rows. -/
theorem changes_filter_castSucc (a z : Coloring α s) (i : Fin s) :
    (changes a z).filter (fun x => z x = i.castSucc) = movedRow a z i := by
  ext x
  simp only [Finset.mem_filter, changes, movedRow, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨hmove, hz⟩
    exact ⟨congrArg Fin.val hz, hmove⟩
  · rintro ⟨hz, hmove⟩
    exact ⟨hmove, Fin.ext hz⟩

omit [DecidableEq α] in
/-- Every changed point has exactly one nonterminal final color. -/
theorem profileSize_profile (a z : Coloring α s) :
    profileSize (profile a z) = (changes a z).card := by
  have hpartition :
      (∑ h : Color s, ((changes a z).filter fun x => z x = h).card) =
        (changes a z).card := by
    simpa using Finset.sum_card_fiberwise_eq_card_filter
      (changes a z) Finset.univ z
  rw [Fin.sum_univ_castSucc, changes_filter_last, Finset.card_empty,
    add_zero] at hpartition
  simp_rw [changes_filter_castSucc] at hpartition
  simpa only [profileSize, rowCount_profile] using hpartition

omit [DecidableEq α] in
theorem profileSize_profile_eq_card_changes (a z : Coloring α s) :
    profileSize (profile a z) = (changes a z).card :=
  profileSize_profile a z

omit [DecidableEq α] in
/-- Entries on or below the diagonal vanish in every actual profile. -/
theorem profile_eq_zero_of_le (a z : Coloring α s) (i : Fin s)
    (h : Color s) (hhi : h.val ≤ i.val) : profile a z i h = 0 := by
  simp [profile, Nat.not_lt.mpr hhi]

/-- The full profile determines every actual crossing count. -/
theorem crossings_eq_profileCrossings (a z : Coloring α s) (i : Fin s) :
    crossings a z i = profileCrossings (profile a z) i := by
  classical
  let C := prefixSet z i \ prefixSet a i
  have hC (x : α) :
      x ∈ C ↔ (z x).val ≤ i.val ∧ i.val < (a x).val := by
    simp [C, prefixSet, not_le]
  have hsplit :
      C.card = ∑ j : Color s, ∑ h : Color s,
        (C.filter fun x => z x = j ∧ a x = h).card := by
    calc
      C.card = ∑ j : Color s, (C.filter fun x => z x = j).card :=
        Finset.card_eq_sum_card_fiberwise
          (s := C) (t := (Finset.univ : Finset (Color s))) (f := z)
          (fun _ _ => Finset.mem_univ _)
      _ = _ := by
        apply Finset.sum_congr rfl
        intro j _
        simpa only [Finset.filter_filter] using
          (Finset.card_eq_sum_card_fiberwise
            (s := C.filter fun x => z x = j)
            (t := (Finset.univ : Finset (Color s))) (f := a)
            (fun _ _ => Finset.mem_univ _))
  have hcell (j h : Color s) :
      (C.filter fun x => z x = j ∧ a x = h) =
        if j.val ≤ i.val ∧ i.val < h.val then
          Finset.univ.filter (fun x =>
            (z x).val = j.val ∧ a x = h ∧ j.val < h.val)
        else ∅ := by
    by_cases hc : j.val ≤ i.val ∧ i.val < h.val
    · rw [ite_eq_left hc]
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨_, hz, ha⟩
        exact ⟨congrArg Fin.val hz, ha, lt_of_le_of_lt hc.1 hc.2⟩
      · rintro ⟨hz, ha, _⟩
        have hz' : z x = j := Fin.ext hz
        refine ⟨(hC x).mpr ?_, hz', ha⟩
        simpa only [hz', ha] using hc
    · rw [ite_eq_right hc]
      apply Finset.filter_eq_empty_iff.mpr
      intro x hx hpair
      rcases hpair with ⟨hz, ha⟩
      apply hc
      simpa only [hz, ha] using (hC x).mp hx
  have hlast :
      (∑ h : Color s,
        (C.filter fun x => z x = Fin.last s ∧ a x = h).card) = 0 := by
    apply Finset.sum_eq_zero
    intro h _
    rw [hcell]
    have hnot : ¬ (Fin.last s).val ≤ i.val :=
      Nat.not_le.mpr i.isLt
    simp only [hnot, false_and, ite_false, Finset.card_empty]
  change C.card = _
  rw [hsplit, Fin.sum_univ_castSucc, hlast, add_zero]
  unfold profileCrossings
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro h _
  rw [hcell]
  by_cases hc : j.val ≤ i.val ∧ i.val < h.val
  · simp only [Fin.val_castSucc, ite_eq_left hc, profile]
  · simp only [Fin.val_castSucc, ite_eq_right hc, Finset.card_empty]

theorem crossings_eq_of_profile_eq (a z : Coloring α s) (n : Profile s)
    (hn : profile a z = n) (i : Fin s) :
    crossings a z i = profileCrossings n i := by
  rw [crossings_eq_profileCrossings, hn]

/-- A row is bounded by the total size of any natural-valued profile. -/
theorem rowCount_le_profileSize (n : Profile s) (i : Fin s) :
    rowCount n i ≤ profileSize n := by
  exact Finset.single_le_sum (fun j _ => Nat.zero_le (rowCount n j))
    (Finset.mem_univ i)

/-- Restricting to entries crossing one level cannot increase total size. -/
theorem profileCrossings_le_profileSize (n : Profile s) (i : Fin s) :
    profileCrossings n i ≤ profileSize n := by
  unfold profileCrossings profileSize rowCount
  apply Finset.sum_le_sum
  intro j _
  apply Finset.sum_le_sum
  intro h _
  split_ifs <;> omega

theorem crossings_le_card_changes (a z : Coloring α s) (i : Fin s) :
    crossings a z i ≤ (changes a z).card := by
  rw [crossings_eq_profileCrossings, ← profileSize_profile a z]
  exact profileCrossings_le_profileSize (profile a z) i

@[simp] theorem mem_groupOriginals {F : Family α} (mu : MassFamily F)
    (a z : Coloring α s) (n : Profile s) :
    a ∈ groupOriginals mu z n ↔ Bad mu a ∧ Selected mu a z ∧ profile a z = n := by
  classical
  simp only [groupOriginals, Finset.mem_filter, Finset.mem_univ, true_and]

end TalagrandThreshold.Selector

end

end OAI
