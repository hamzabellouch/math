import OAI.NumberTheory.Ostmann.Construction.InsertedConstituentWords
import OAI.NumberTheory.Ostmann.Construction.WordPrimeCheckBound

namespace OAI

/-! # Every reconstructed prime check excludes the fixed pivot coordinate -/

namespace Ostmann

open scoped Classical

def ExpandedUnfixedCoordinates {I V : Type*} (role : I → CopyScheduleRole)
    (depth n : ℕ)
    (current : CopyScheduleAtoms role n → List (ExpandedScheduledVariable (Option V) depth)) : Prop :=
  ∀ i, (∀ k, copyScheduleRole role n i.val ≠ .pivot k) →
    ∀ v ∈ current i, ∃ a : V, v = .inl (some a)

theorem reverseExpandedUnfixedCoordinates {I V : Type*} (role : I → CopyScheduleRole)
    (depth n : ℕ) (b : Bool) (pivot : ExpandedScheduledVariable (Option V) depth)
    (current : CopyScheduleAtoms role (n + 1) → List (ExpandedScheduledVariable (Option V) depth))
    (hc : ExpandedUnfixedCoordinates role depth (n + 1) current) :
    ExpandedUnfixedCoordinates role depth n (reverseCopyLabelMap role n b [pivot] current) := by
  intro i hi v hv
  unfold reverseCopyLabelMap at hv
  split_ifs at hv with hcopy herase
  · apply hc _ _ v hv
    intro k hk
    change (copyScheduleRole role n i.val).afterCopy b = .pivot k at hk
    exact hi k ((CopyScheduleRole.afterCopy_eq_pivot _ b k).mp hk).2
  · have he := herase
    cases hr : copyScheduleRole role n i.val <;>
      simp only [hr, CopyScheduleRole.erasedAt, Bool.false_eq_true] at he
    rename_i k
    exact False.elim (hi k hr)
  · apply hc _ ?_ v hv
    intro k hk
    exact hi k hk

theorem inserted_root_unfixed_coordinates {I : Type*} (role : I → CopyScheduleRole)
    (size : I → ℕ) (n : ℕ) :
    ExpandedUnfixedCoordinates role n n
      (fun i => (insertedConstituentWord role size n i).map Sum.inl) := by
  intro i hi v hv
  obtain ⟨a, rfl⟩ := (scheduledPartitionEquiv role n).surjective i
  rcases a with p | h | y
  · exact False.elim (hi n (copyScheduleRole_positive role p.val n p.property n))
  · simp only [insertedConstituentWord, Equiv.symm_apply_apply, List.mem_map, List.mem_ofFn] at hv
    obtain ⟨z, ⟨k, rfl⟩, rfl⟩ := hv
    exact ⟨.inl (constituentH role size n h k), rfl⟩
  · simp only [insertedConstituentWord, Equiv.symm_apply_apply, List.mem_map, List.mem_ofFn] at hv
    obtain ⟨z, ⟨k, rfl⟩, rfl⟩ := hv
    exact ⟨.inr (constituentY role size n y k), rfl⟩

theorem mem_expandedOriginalWord_iff {V : Type*} {depth : ℕ}
    (w : List (ExpandedScheduledVariable V depth)) (v : V) :
    v ∈ expandedOriginalWord w ↔ Sum.inl v ∈ w := by
  induction w with
  | nil => simp [expandedOriginalWord]
  | cons a w ih => cases a <;> simp [expandedOriginalWord, ih]

theorem expandedYPrimeCoordinates_ne_none {I V : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (depth n : ℕ)
    (current : CopyScheduleAtoms role (n + 1) → List (ExpandedScheduledVariable (Option V) depth))
    (hc : ExpandedUnfixedCoordinates role depth (n + 1) current) :
    ∀ v ∈ expandedYPrimeCoordinates role depth n current, v ≠ none := by
  intro v hv he
  subst v
  obtain ⟨i, _, hi⟩ := List.mem_flatMap.mp hv
  have hm := (mem_expandedOriginalWord_iff _ none).mp hi
  obtain ⟨a, ha⟩ := hc ⟨.inr i.val, i.property⟩
    (fun k => copyScheduleY_not_pivot role n i k) _ hm
  cases ha

def WordPrimeDecoration.Coordinates {V : Type*} (p : V → Prop) :
    {n : ℕ} → WordPrimeDecoration V n → Prop
  | 0, .leaf => True
  | _ + 1, .node xs l r => (∀ v ∈ xs, p v) ∧ l.Coordinates p ∧ r.Coordinates p

theorem expandedSchedulePrimes_unfixed {I V : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (depth n : ℕ) (path : List Bool)
    (current : CopyScheduleAtoms role n → List (ExpandedScheduledVariable (Option V) depth))
    (hc : ExpandedUnfixedCoordinates role depth n current) :
    (expandedSchedulePrimes role depth n path current).Coordinates (· ≠ none) := by
  induction n generalizing path with
  | zero => trivial
  | succ n ih =>
    exact ⟨expandedYPrimeCoordinates_ne_none role depth n current hc,
      ih (true :: path) _ (reverseExpandedUnfixedCoordinates role depth n true _ current hc),
      ih (false :: path) _ (reverseExpandedUnfixedCoordinates role depth n false _ current hc)⟩

theorem WordPrimeDecoration.checks_coordinates {V σ : Type*} {n : ℕ}
    (D : WordPrimeDecoration V n) (p : V → Prop) (hD : D.Coordinates p)
    (template : WordTransferTemplate σ n) (t : FrequencyTree ℤ n)
    (ht : NonzeroInternalFrequencies n t) (env : σ → HistoryFormula σ) :
    ∀ g ∈ D.checks template t ht env, p g.coordinate := by
  induction template generalizing env with
  | leaf word => cases D; simp [checks]
  | @node n d l r ihl ihr =>
    cases D with
    | node xs L R =>
      intro g hg
      rcases List.mem_append.mp hg with hg | hg
      · obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hg
        exact hD.1 v hv
      · rcases List.mem_append.mp hg with hg | hg
        · exact ihl L hD.2.1 t.2.1 ht.2.1 _ g hg
        · exact ihr R hD.2.2 t.2.2 ht.2.2 _ g hg

theorem WordPrimeDecoration.checkAt_unfixed {V σ : Type*} {n : ℕ}
    (D : WordPrimeDecoration (Option V) n) (hD : D.Coordinates (· ≠ none))
    (template : WordTransferTemplate σ n) (t : FrequencyTree ℤ n)
    (ht : NonzeroInternalFrequencies n t) (i : Fin D.count) :
    ∃ v, (D.checkAt template t ht i).coordinate = some v := by
  have h := D.checks_coordinates (· ≠ none) hD template t ht .prime
    _ (D.checkAt_mem template t ht i)
  cases he : (D.checkAt template t ht i).coordinate with
  | none => exact False.elim (h he)
  | some v => exact ⟨v, rfl⟩

theorem insertedSchedulePrimes_unfixed {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (size : I → ℕ) (n : ℕ) :
    (expandedSchedulePrimes role n n []
      (fun i => (insertedConstituentWord role size n i).map Sum.inl)).Coordinates (· ≠ none) :=
  expandedSchedulePrimes_unfixed role n n [] _ (inserted_root_unfixed_coordinates role size n)

theorem inserted_permuted_root_unfixed_coordinates {I : Type*} (role : I → CopyScheduleRole)
    (size : I → ℕ) (n : ℕ)
    (e : Equiv.Perm (CopyScheduleH (fun i : Σ a, Fin (size a) => role i.1) n)) :
    ExpandedUnfixedCoordinates role n n (fun i =>
      ((insertedConstituentWord role size n i).map
        (insertedConstituentPerm role size n e)).map Sum.inl) := by
  intro i hi v hv
  obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hv
  obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hw
  have hroot := inserted_root_unfixed_coordinates role size n i hi (.inl z)
    (List.mem_map.mpr ⟨z, hz, rfl⟩)
  obtain ⟨a, ha⟩ := hroot
  have hza : z = some a := Sum.inl.inj ha
  subst z
  exact ⟨_, rfl⟩

theorem insertedPermutedSchedulePrimes_unfixed {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (size : I → ℕ) (n : ℕ)
    (e : Equiv.Perm (CopyScheduleH (fun i : Σ a, Fin (size a) => role i.1) n)) :
    (expandedSchedulePrimes role n n [] (fun i =>
      ((insertedConstituentWord role size n i).map
        (insertedConstituentPerm role size n e)).map Sum.inl)).Coordinates (· ≠ none) :=
  expandedSchedulePrimes_unfixed role n n [] _
    (inserted_permuted_root_unfixed_coordinates role size n e)

end Ostmann

end OAI
