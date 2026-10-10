import OAI.NumberTheory.Ostmann.Construction.ConstituentUnweighted

namespace OAI

/-! # Word coordinates for the fixed integer pivot and the retained primes -/

namespace Ostmann

open scoped BigOperators Classical

abbrev InsertedConstituentVariable {I : Type*} (role : I → CopyScheduleRole)
    (size : I → ℕ) (n : ℕ) :=
  Option (CopyScheduleH (fun i : Σ a, Fin (size a) => role i.1) n ⊕
    CopyScheduleY (fun i : Σ a, Fin (size a) => role i.1) n)

def insertedConstituentValues {I : Type*} (role : I → CopyScheduleRole)
    (size : I → ℕ) (n : ℕ) (M : ℕ)
    (l : CopyScheduleH (fun i : Σ a, Fin (size a) => role i.1) n → ℕ)
    (u : CopyScheduleY (fun i : Σ a, Fin (size a) => role i.1) n → ℕ) :
    InsertedConstituentVariable role size n → ℕ
  | none => M
  | some (.inl h) => l h
  | some (.inr y) => u y

noncomputable def insertedConstituentWord {I : Type*} (role : I → CopyScheduleRole)
    (size : I → ℕ) (n : ℕ) (v : CopyScheduleAtoms role n) :
    List (InsertedConstituentVariable role size n) :=
  match (scheduledPartitionEquiv role n).symm v with
  | .inl _ => [none]
  | .inr (.inl h) => List.ofFn (fun k => some (.inl (constituentH role size n h k)))
  | .inr (.inr y) => List.ofFn (fun k => some (.inr (constituentY role size n y k)))

theorem insertedConstituentWord_prod {I : Type*} (role : I → CopyScheduleRole)
    (size : I → ℕ) (n : ℕ) (M : ℕ)
    (l : CopyScheduleH (fun i : Σ a, Fin (size a) => role i.1) n → ℕ)
    (u : CopyScheduleY (fun i : Σ a, Fin (size a) => role i.1) n → ℕ)
    (v : CopyScheduleAtoms role n) :
    ((insertedConstituentWord role size n v).map (insertedConstituentValues role size n M l u)).prod =
      scheduledInsertedAtoms role n M
        (fun h => ∏ k, l (constituentH role size n h k))
        (fun y => ∏ k, u (constituentY role size n y k)) v := by
  obtain ⟨a, rfl⟩ := (scheduledPartitionEquiv role n).surjective v
  rcases a with p | h | y <;>
    simp only [insertedConstituentWord, scheduledInsertedAtoms, Equiv.symm_apply_apply,
      List.map_singleton, List.prod_singleton, List.map_ofFn, List.prod_ofFn,
      Function.comp_apply, insertedConstituentValues]

theorem insertedConstituentWord_length_le {I : Type*} (role : I → CopyScheduleRole)
    (size : I → ℕ) (n S : ℕ) (hS : 1 ≤ S) (hsize : ∀ i, size i ≤ S)
    (v : CopyScheduleAtoms role n) : (insertedConstituentWord role size n v).length ≤ S := by
  obtain ⟨a, rfl⟩ := (scheduledPartitionEquiv role n).surjective v
  rcases a with p | h | y
  · simpa only [insertedConstituentWord, Equiv.symm_apply_apply, List.length_singleton] using hS
  · simpa only [insertedConstituentWord, Equiv.symm_apply_apply, List.length_ofFn] using
      hsize (copyScheduleOrigin n h.val)
  · simpa only [insertedConstituentWord, Equiv.symm_apply_apply, List.length_ofFn] using
      hsize (copyScheduleOrigin n y.val)

def insertedConstituentPerm {I : Type*} (role : I → CopyScheduleRole)
    (size : I → ℕ) (n : ℕ)
    (e : Equiv.Perm (CopyScheduleH (fun i : Σ a, Fin (size a) => role i.1) n)) :
    Equiv.Perm (InsertedConstituentVariable role size n) :=
  Equiv.optionCongr (Equiv.sumCongr e (Equiv.refl _))

theorem insertedConstituentValues_perm {I : Type*} (role : I → CopyScheduleRole)
    (size : I → ℕ) (n : ℕ) (M : ℕ)
    (l : CopyScheduleH (fun i : Σ a, Fin (size a) => role i.1) n → ℕ)
    (u : CopyScheduleY (fun i : Σ a, Fin (size a) => role i.1) n → ℕ)
    (e : Equiv.Perm (CopyScheduleH (fun i : Σ a, Fin (size a) => role i.1) n)) :
    insertedConstituentValues role size n M l u ∘ insertedConstituentPerm role size n e =
      insertedConstituentValues role size n M (l ∘ e) u := by
  funext v
  rcases v with _ | (h | y) <;> rfl

end Ostmann

end OAI
