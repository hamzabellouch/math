import OAI.NumberTheory.Ostmann.Construction.ScheduledTemplateBounds

namespace OAI

/-! # The atom schedule expanded into its actual prime constituents -/

namespace Ostmann

open scoped BigOperators Classical

noncomputable def expandedHWord {I σ : Type*} [Fintype I] (role : I → CopyScheduleRole)
    (n : ℕ) (b : Bool) (current : CopyScheduleAtoms role (n + 1) → List σ) : List σ :=
  (Finset.univ.toList : List (CopyScheduleH role n)).flatMap fun i =>
    current ⟨.inl (b, i.val), i.property⟩

/-- Actual atoms may have several prime constituents. An erased pivot is
replaced by its single reconstructed total; all other atoms retain their lists. -/
noncomputable def expandedScheduledTemplate {I σ : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (address : ℕ → List Bool → σ) (childBound pivotBound : ℕ → ℕ) :
    (n : ℕ) → List Bool → (CopyScheduleAtoms role n → List σ) → WordTransferTemplate σ n
  | 0, _, current => .leaf ((Finset.univ.toList : List (CopyScheduleAtoms role 0)).flatMap current)
  | n + 1, path, current =>
      .node ⟨address n path, expandedHWord role n true current, expandedHWord role n false current,
        childBound n, pivotBound n⟩
        (expandedScheduledTemplate role address childBound pivotBound n (true :: path)
          (reverseCopyLabelMap role n true [address n path] current))
        (expandedScheduledTemplate role address childBound pivotBound n (false :: path)
          (reverseCopyLabelMap role n false [address n path] current))

theorem list_flatMap_length_bound {α β : Type*} (l : List α) (f : α → List β) (M : ℕ)
    (h : ∀ a ∈ l, (f a).length ≤ M) : (l.flatMap f).length ≤ l.length * M := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_cons]
    have ha := h a (by simp)
    have hl := ih (fun b hb => h b (by simp [hb]))
    nlinarith

theorem reverseCopyLabelMap_list_length {I σ : Type*} (role : I → CopyScheduleRole)
    (n : ℕ) (b : Bool) (pivot : σ) (current : CopyScheduleAtoms role (n + 1) → List σ)
    (M : ℕ) (hM : 1 ≤ M) (hc : ∀ i, (current i).length ≤ M) :
    ∀ i, (reverseCopyLabelMap role n b [pivot] current i).length ≤ M := by
  intro i
  unfold reverseCopyLabelMap
  split_ifs
  · exact hc _
  · exact hM
  · exact hc _

theorem expandedHWord_length {I σ : Type*} [Fintype I] (role : I → CopyScheduleRole)
    (n : ℕ) (b : Bool) (current : CopyScheduleAtoms role (n + 1) → List σ)
    (M : ℕ) (hc : ∀ i, (current i).length ≤ M) :
    (expandedHWord role n b current).length ≤ Fintype.card (CopyScheduleH role n) * M := by
  simpa only [expandedHWord, Finset.length_toList, Finset.card_univ] using
    list_flatMap_length_bound (Finset.univ.toList : List (CopyScheduleH role n))
      (fun i => current ⟨.inl (b, i.val), i.property⟩) M (fun _ _ => hc _)

theorem expandedScheduledTemplate_words_bounded {I σ : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (address : ℕ → List Bool → σ) (childBound pivotBound : ℕ → ℕ)
    (n M B : ℕ) (hM : 1 ≤ M) (hbase : Fintype.card (CopyScheduleAtoms role 0) * M + 1 ≤ B)
    (hH : ∀ j < n, 2 * Fintype.card (CopyScheduleH role j) * M + 4 ≤ B)
    (path : List Bool) (current : CopyScheduleAtoms role n → List σ)
    (hc : ∀ i, (current i).length ≤ M) :
    (expandedScheduledTemplate role address childBound pivotBound n path current).WordsBounded B := by
  induction n generalizing path with
  | zero =>
    change (List.flatMap current (Finset.univ.toList : List (CopyScheduleAtoms role 0))).length + 1 ≤ B
    have hh := list_flatMap_length_bound (Finset.univ.toList : List (CopyScheduleAtoms role 0)) current M
      (fun i _ => hc i)
    simp only [Finset.length_toList, Finset.card_univ] at hh
    omega
  | succ n ih =>
    change _ ∧ _ ∧ _
    refine ⟨?_, ih (fun j hj => hH j (by omega)) _ _
      (reverseCopyLabelMap_list_length role n true _ current M hM hc),
      ih (fun j hj => hH j (by omega)) _ _
      (reverseCopyLabelMap_list_length role n false _ current M hM hc)⟩
    have hL := expandedHWord_length role n true current M hc
    have hR := expandedHWord_length role n false current M hc
    have hh := hH n (by omega)
    dsimp only
    nlinarith

theorem list_flatMap_product {α σ : Type*} (l : List α) (f : α → List σ) (x : σ → ℕ) :
    ((l.flatMap f).map x).prod = (l.map (fun a => ((f a).map x).prod)).prod := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.flatMap_cons, List.map_append, List.prod_append, List.map_cons, List.prod_cons, ih]

theorem expandedHWord_product {I σ : Type*} [Fintype I] (role : I → CopyScheduleRole)
    (n : ℕ) (b : Bool) (current : CopyScheduleAtoms role (n + 1) → List σ) (x : σ → ℕ) :
    ((expandedHWord role n b current).map x).prod =
      ∏ i : CopyScheduleH role n, ((current ⟨.inl (b, i.val), i.property⟩).map x).prod := by
  rw [expandedHWord, list_flatMap_product]
  exact Finset.prod_map_toList _ _

end Ostmann

end OAI
