import OAI.NumberTheory.Ostmann.Construction.ReverseCopyMap
import OAI.NumberTheory.Ostmann.Construction.WordTransferFormulaBounds

namespace OAI

/-! # The word-transfer template constructed from the actual copied-atom schedule -/

namespace Ostmann

open scoped BigOperators Classical

noncomputable def scheduledHWord {I σ : Type*} [Fintype I] (role : I → CopyScheduleRole)
    (n : ℕ) (b : Bool) (current : CopyScheduleAtoms role (n + 1) → σ) : List σ :=
  (Finset.univ.toList : List (CopyScheduleH role n)).map fun i =>
    current ⟨.inl (b, i.val), i.property⟩

/-- Each internal address names the product of the pivot atom erased at
that node. Both child templates read the same Y and their own H copies. -/
noncomputable def scheduledWordTemplate {I σ : Type*} [Fintype I] (role : I → CopyScheduleRole)
    (address : ℕ → List Bool → σ) (childBound pivotBound : ℕ → ℕ) :
    (n : ℕ) → List Bool → (CopyScheduleAtoms role n → σ) → WordTransferTemplate σ n
  | 0, _, current => .leaf ((Finset.univ.toList : List (CopyScheduleAtoms role 0)).map current)
  | n + 1, path, current =>
      .node ⟨address n path, scheduledHWord role n true current,
        scheduledHWord role n false current, childBound n, pivotBound n⟩
        (scheduledWordTemplate role address childBound pivotBound n (true :: path)
          (reverseCopyLabelMap role n true (address n path) current))
        (scheduledWordTemplate role address childBound pivotBound n (false :: path)
          (reverseCopyLabelMap role n false (address n path) current))

theorem scheduledHWord_length {I σ : Type*} [Fintype I] (role : I → CopyScheduleRole)
    (n : ℕ) (b : Bool) (current : CopyScheduleAtoms role (n + 1) → σ) :
    (scheduledHWord role n b current).length = Fintype.card (CopyScheduleH role n) := by
  simp only [scheduledHWord, List.length_map, Finset.length_toList, Finset.card_univ]

/-- The word-size bound is inherited from the literal H partition sizes;
no independent polynomial-size hypothesis is imposed on the resulting template. -/
theorem scheduledWordTemplate_words_bounded {I σ : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (address : ℕ → List Bool → σ)
    (childBound pivotBound : ℕ → ℕ) (n : ℕ) (B : ℕ)
    (hbase : Fintype.card (CopyScheduleAtoms role 0) + 1 ≤ B)
    (hH : ∀ j < n, 2 * Fintype.card (CopyScheduleH role j) + 4 ≤ B)
    (path : List Bool) (current : CopyScheduleAtoms role n → σ) :
    (scheduledWordTemplate role address childBound pivotBound n path current).WordsBounded B := by
  induction n generalizing path with
  | zero =>
    simpa only [scheduledWordTemplate, WordTransferTemplate.WordsBounded,
      List.length_map, Finset.length_toList, Finset.card_univ] using hbase
  | succ n ih =>
    change _ ∧ _ ∧ _
    refine ⟨?_, ih (fun j hj => hH j (by omega)) _ _, ih (fun j hj => hH j (by omega)) _ _⟩
    simp only [scheduledHWord_length]
    have hh := hH n (by omega)
    omega

theorem scheduledHWord_product {I σ : Type*} [Fintype I] (role : I → CopyScheduleRole)
    (n : ℕ) (b : Bool) (current : CopyScheduleAtoms role (n + 1) → σ) (x : σ → ℕ) :
    ((scheduledHWord role n b current).map x).prod =
      ∏ i : CopyScheduleH role n, x (current ⟨.inl (b, i.val), i.property⟩) := by
  simp only [scheduledHWord, List.map_map, Function.comp_def]
  exact Finset.prod_map_toList _ _

/-- The numerator products at the top node are precisely its independent
positive and negative H copies. -/
theorem scheduledWordTemplate_products {I σ : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (address : ℕ → List Bool → σ)
    (childBound pivotBound : ℕ → ℕ) (n : ℕ) (path : List Bool)
    (current : CopyScheduleAtoms role (n + 1) → σ) (x : σ → ℕ) :
    wordTransferLeft ((scheduledWordTemplate role address childBound pivotBound (n + 1) path current).state x) =
      (∏ i : CopyScheduleH role n, x (current ⟨.inl (true, i.val), i.property⟩)) ∧
    wordTransferRight ((scheduledWordTemplate role address childBound pivotBound (n + 1) path current).state x) =
      (∏ i : CopyScheduleH role n, x (current ⟨.inl (false, i.val), i.property⟩)) :=
  ⟨scheduledHWord_product role n true current x, scheduledHWord_product role n false current x⟩

end Ostmann

end OAI
