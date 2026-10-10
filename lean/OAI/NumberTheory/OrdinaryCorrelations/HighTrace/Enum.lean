import Mathlib

namespace OAI

noncomputable section
open scoped BigOperators
open Finset
open Finset Classical
open Filter
open Finset Classical Filter

namespace OrdinaryCorrelations.FiniteSlotEncoding
variable {P : Type*} [DecidableEq P]

def enum (s : Finset P) : Fin s.card ≃ s :=
  (Fintype.equivFinOfCardEq (Fintype.card_coe s)).symm

def code (s : Finset P) (m : ℕ) (i : Fin m) : Option P :=
  if hi : i.val < s.card then some ((enum s) ⟨i.val,hi⟩).val else none

omit [DecidableEq P] in
lemma mem_iff_code (s : Finset P) (m : ℕ) (hs : s.card ≤ m) (p : P) :
    p ∈ s ↔ ∃ i : Fin m, code s m i=some p := by
  constructor
  · intro hp
    let i := (enum s).symm ⟨p,hp⟩
    refine ⟨⟨i.val,lt_of_lt_of_le i.isLt hs⟩,?_⟩
    simp only [code,dite_eq_left i.isLt]
    have he : (enum s) i=⟨p,hp⟩ := (enum s).apply_symm_apply _
    exact congrArg (fun z : s => some z.val) he
  · rintro ⟨i,hi⟩
    unfold code at hi
    split_ifs at hi with h
    · exact Option.some.inj hi ▸ ((enum s) ⟨i.val,h⟩).property

omit [DecidableEq P] in
lemma code_injective {s t : Finset P} {m : ℕ} (hs : s.card ≤ m) (ht : t.card ≤ m)
    (he : code s m=code t m) : s=t := by
  ext p
  rw [mem_iff_code s m hs p,mem_iff_code t m ht p,he]

omit [DecidableEq P] in
lemma code_mem (s : Finset P) (m : ℕ) (i : Fin m) (p : P)
    (hi : code s m i=some p) : p ∈ s := by
  unfold code at hi
  split_ifs at hi with h
  · exact Option.some.inj hi ▸ ((enum s) ⟨i.val,h⟩).property

omit [DecidableEq P] in
lemma none_iff (s : Finset P) (m : ℕ) (i : Fin m) :
    code s m i=none ↔ s.card ≤ i.val := by
  unfold code
  split_ifs <;> simp_all

theorem code_support (s : Finset P) (m : ℕ) (hs : s.card ≤ m) :
    (univ.biUnion (fun i : Fin m => (code s m i).toFinset))=s := by
  ext p
  simp only [mem_biUnion,mem_univ,true_and,Option.mem_toFinset]
  exact (mem_iff_code s m hs p).symm

end OrdinaryCorrelations.FiniteSlotEncoding

end

end OAI
