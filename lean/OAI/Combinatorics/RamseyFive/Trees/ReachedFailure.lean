import Mathlib
import OAI.Combinatorics.RamseyFive.Trees.TreeOriginalTrims

namespace OAI

namespace SharpRamseyFive.TreeCodec
open FiniteEntropy BinaryTree
open scoped Classical BigOperators
noncomputable section
local instance (priority := high) allPropDecidable (P : Prop) : Decidable P := Classical.propDecidable P
universe u v w z
variable {I : Type u} {C : Type v} [Fintype C]
  (Ω : I → C → Type w) [∀ i c, Fintype (Ω i c)]
  (M : ∀ i c, Ω i c → Type z) (left right : ∀ i c t, M i c t → C)
  (enc : ∀ i c t, Option (M i c t))

noncomputable def flagTest (P : ∀ i c, Ω i c → Prop) :=
  fun i c t => if P i c t then some () else none

noncomputable def flagAt (P : ∀ i c, Ω i c → Prop)
    (b : BinaryTree I) (ω : Tape Ω b) (c : C) (j : Address b) : Option Unit :=
  probe Ω M left right enc (flagTest Ω P) b ω c j

omit [Fintype C] [∀ index context, Fintype (Ω index context)] in
lemma flagAt_mono (P Q : ∀ i c, Ω i c → Prop)
    (h : ∀ i c t, P i c t → Q i c t) (b : BinaryTree I) (ω : Tape Ω b) (c : C) (j : Address b) :
    flagAt Ω M left right enc P b ω c j = some () →
      flagAt Ω M left right enc Q b ω c j = some () := by
  induction b generalizing c with
  | nil => exact nomatch j
  | node i l r ihl ihr =>
    rcases j with j | (j | j)
    · by_cases hp : P i c (ω.1 c) <;> by_cases hq : Q i c (ω.1 c) <;> simp_all [flagAt, flagTest, probe]
    · cases he : enc i c (ω.1 c) with
      | none => simp [flagAt, probe, he]
      | some m => simpa only [flagAt, probe, he, Option.map_some, Option.elim_some] using ihl ω.2.1 (left i c (ω.1 c) m) j
    · cases he : enc i c (ω.1 c) with
      | none => simp [flagAt, probe, he]
      | some m => simpa only [flagAt, probe, he, Option.map_some, Option.elim_some] using ihr ω.2.2 (right i c (ω.1 c) m) j

omit [Fintype C] [∀ index context, Fintype (Ω index context)] in
lemma flagAt_or (P Q : ∀ i c, Ω i c → Prop)
    (b : BinaryTree I) (ω : Tape Ω b) (c : C) (j : Address b) :
    flagAt Ω M left right enc (fun i c t => P i c t ∨ Q i c t) b ω c j = some () ↔
      flagAt Ω M left right enc P b ω c j = some () ∨
      flagAt Ω M left right enc Q b ω c j = some () := by
  induction b generalizing c with
  | nil => exact nomatch j
  | node i l r ihl ihr =>
    rcases j with j | (j | j)
    · by_cases hp : P i c (ω.1 c) <;> by_cases hq : Q i c (ω.1 c) <;> simp [flagAt, flagTest, probe, hp, hq]
    · cases he : enc i c (ω.1 c) with
      | none => simp [flagAt, probe, he]
      | some m => simpa only [flagAt, probe, he, Option.map_some, Option.elim_some] using ihl ω.2.1 (left i c (ω.1 c) m) j
    · cases he : enc i c (ω.1 c) with
      | none => simp [flagAt, probe, he]
      | some m => simpa only [flagAt, probe, he, Option.map_some, Option.elim_some] using ihr ω.2.2 (right i c (ω.1 c) m) j

omit [Fintype C] [∀ index context, Fintype (Ω index context)] in
lemma flagAt_context (P : I → C → Prop)
    (b : BinaryTree I) (ω : Tape Ω b) (c : C) (j : Address b) :
    flagAt Ω M left right enc (fun i c _ => P i c) b ω c j = some () ↔
      ∃ c', contextAt Ω M left right enc b ω c j = some c' ∧ P (label b j) c' := by
  induction b generalizing c with
  | nil => exact nomatch j
  | node i l r ihl ihr =>
    rcases j with j | (j | j)
    · simp [flagAt, flagTest, contextAt, probe, label]
    · cases he : enc i c (ω.1 c) with
      | none => simp [flagAt, contextAt, probe, he]
      | some m => simpa only [flagAt, contextAt, probe, he, Option.map_some, Option.elim_some, label] using ihl ω.2.1 (left i c (ω.1 c) m) j
    · cases he : enc i c (ω.1 c) with
      | none => simp [flagAt, contextAt, probe, he]
      | some m => simpa only [flagAt, contextAt, probe, he, Option.map_some, Option.elim_some, label] using ihr ω.2.2 (right i c (ω.1 c) m) j

omit [Fintype C] [∀ index context, Fintype (Ω index context)] in
lemma flagAt_abort (b : BinaryTree I) (ω : Tape Ω b) (c : C) (j : Address b) :
    flagAt Ω M left right enc (fun i c t => enc i c t = none) b ω c j = some () ↔
      abortAt Ω M left right enc b ω c j = some true := by
  induction b generalizing c with
  | nil => exact nomatch j
  | node i l r ihl ihr =>
    rcases j with j | (j | j)
    · cases he : enc i c (ω.1 c) <;> simp [flagAt, flagTest, abortAt, probe, he]
    · cases he : enc i c (ω.1 c) with
      | none => simp [flagAt, abortAt, probe, he]
      | some m => simpa only [flagAt, abortAt, probe, he, Option.map_some, Option.elim_some] using ihl ω.2.1 (left i c (ω.1 c) m) j
    · cases he : enc i c (ω.1 c) with
      | none => simp [flagAt, abortAt, probe, he]
      | some m => simpa only [flagAt, abortAt, probe, he, Option.map_some, Option.elim_some] using ihr ω.2.2 (right i c (ω.1 c) m) j

lemma flagAt_bound (p : ∀ i c, Law (Ω i c)) (P : ∀ i c, Ω i c → Prop)
    (ε : I → ℝ) (hε : ∀ i, 0≤ε i)
    (hlocal : ∀ i c, eventMass (p i c) (Finset.univ.filter (P i c)) ≤ ε i)
    (b : BinaryTree I) (c : C) (j : Address b) :
    eventMass (tapeLaw Ω p b) (Finset.univ.filter (fun ω =>
      flagAt Ω M left right enc P b ω c j = some ())) ≤ ε (label b j) := by
  have h := probe_event_bound Ω M left right p enc (flagTest Ω P) (fun x => x = some ())
    (by simp) ε hε ?_ b c j
  · rw [eventMass_map_filter] at h
    convert h using 1; congr 2
  · intro i c
    rw [eventMass_map_filter]
    simpa [flagTest] using hlocal i c

theorem reached_abort_bound (p : ∀ i c, Law (Ω i c)) (ready : I → C → Prop)
    (ε : I → ℝ) (hε : ∀ i, 0≤ε i)
    (hlocal : ∀ i c, ready i c →
      eventMass (p i c) (Finset.univ.filter (fun t => enc i c t = none)) ≤ ε i)
    (b : BinaryTree I) (c : C) (j : Address b) :
    eventMass (tapeLaw Ω p b) (Finset.univ.filter (fun ω =>
      abortAt Ω M left right enc b ω c j = some true)) ≤
    eventMass (tapeLaw Ω p b) (Finset.univ.filter (fun ω => ∃ c',
      contextAt Ω M left right enc b ω c j = some c' ∧ ¬ready (label b j) c')) + ε (label b j) := by
  let P := fun i c (_ : Ω i c) => ¬ ready i c
  let Q := fun i c (t : Ω i c) => ready i c ∧ enc i c t = none
  have hs (ω : Tape Ω b) : abortAt Ω M left right enc b ω c j = some true →
      (∃ c', contextAt Ω M left right enc b ω c j = some c' ∧ ¬ ready (label b j) c') ∨
      flagAt Ω M left right enc Q b ω c j = some () := by
    intro hh
    have h := (flagAt_abort Ω M left right enc b ω c j).mpr hh
    have h' := flagAt_mono Ω M left right enc _ (fun i c t => P i c t ∨ Q i c t)
      (fun i c t ht => by by_cases hr : ready i c; exact Or.inr ⟨hr, ht⟩; exact Or.inl hr) b ω c j h
    rw [flagAt_or] at h'
    exact h'.imp (fun ha => (flagAt_context Ω M left right enc (fun i c => ¬ready i c) b ω c j).mp ha) id
  have hg : eventMass (tapeLaw Ω p b) (Finset.univ.filter (fun ω =>
      flagAt Ω M left right enc Q b ω c j = some ())) ≤ ε (label b j) := by
    apply flagAt_bound Ω M left right enc p Q ε hε
    intro i c
    by_cases hr : ready i c
    · simpa [Q, hr] using hlocal i c hr
    · simpa [Q, hr, eventMass] using hε i
  calc
    _ ≤ eventMass (tapeLaw Ω p b) (Finset.univ.filter (fun ω =>
        (∃ c', contextAt Ω M left right enc b ω c j = some c' ∧ ¬ready (label b j) c') ∨
        flagAt Ω M left right enc Q b ω c j = some ())) := eventMass_filter_mono _ _ _ hs
    _ ≤ _ := by
      have hu := eventMass_filter_union (tapeLaw Ω p b)
        (fun ω => ∃ c', contextAt Ω M left right enc b ω c j = some c' ∧ ¬ready (label b j) c')
        (fun ω => flagAt Ω M left right enc Q b ω c j = some ())
      convert hu.trans (add_le_add le_rfl hg) using 1; congr
end
end SharpRamseyFive.TreeCodec

end OAI
