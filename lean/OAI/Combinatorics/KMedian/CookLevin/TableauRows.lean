import Mathlib
import OAI.Combinatorics.KMedian.Expanders.Stopped

namespace OAI

section Inline_PCPTableauRows

namespace MetricKMedian.PCP.Tableau
open scoped Classical

variable {A : Type}
lemma blank_propagates (f : ℕ → Option A) (L : ℕ)
    (h : ∀ i<L, f i=none → f (i+1)=none) (h0 : f 0=none) :
    ∀ i≤L, f i=none := by
  intro i hi
  induction i with
  | zero => exact h0
  | succ i ih => exact h i (by omega) (ih (by omega))
lemma row_list (f : ℕ → Option A) (L : ℕ) (hend : f L=none)
    (h : ∀ i<L, f i=none → f (i+1)=none) :
    ∃ l : List A, l.length≤L ∧ ∀ i≤L, l[i]?=f i := by
  induction L generalizing f with
  | zero =>
    refine ⟨[],by simp,?_⟩
    intro i hi
    have he : i=0 := by omega
    subst i
    simpa using hend.symm
  | succ L ih =>
    cases h0 : f 0 with
    | none =>
      exact ⟨[],by simp,fun i hi => by simpa using (blank_propagates f (L+1) h h0 i hi).symm⟩
    | some a =>
      obtain ⟨l,hl,he⟩ := ih (fun i => f (i+1)) hend (by
        intro i hi hn
        exact h (i+1) (by omega) hn)
      refine ⟨a::l,by simp only [List.length_cons]; omega,?_⟩
      intro i hi
      cases i with
      | zero => simpa using h0.symm
      | succ i => simpa using he i (by omega)

abbrev Row (A : Type) (L : ℕ) := Fin (L+1) → Option A
def rowCell (L : ℕ) (row : Row A L) (i : ℕ) : Option A :=
  if h : i≤L then row ⟨i,by omega⟩ else none
def ValidRow (L : ℕ) (row : Row A L) : Prop :=
  row ⟨L,by omega⟩=none ∧ ∀ i : Fin L,
    row ⟨i.val,by omega⟩=none → row ⟨i.val+1,by omega⟩=none
lemma valid_row_list (L : ℕ) (row : Row A L) (h : ValidRow L row) :
    ∃ l : List A, l.length≤L ∧ ∀ i, l[i]?=rowCell L row i := by
  obtain ⟨l,hl,he⟩ := row_list (rowCell L row) L
    (by simpa only [rowCell,dite_eq_left (Nat.le_refl L)] using h.1)
    (by
      intro i hi hn
      simp only [rowCell,dite_eq_left (by omega : i≤L)] at hn
      simpa only [rowCell,dite_eq_left (by omega : i+1≤L)] using h.2 ⟨i,hi⟩ hn)
  refine ⟨l,hl,?_⟩
  intro i
  by_cases hi : i≤L
  · exact he i hi
  · rw [List.getElem?_eq_none (by omega),rowCell,dite_eq_right hi]
def listRow (L : ℕ) (l : List A) : Row A L := fun i => l[i.val]?
lemma listRow_valid (L : ℕ) (l : List A) (h : l.length≤L) : ValidRow L (listRow L l) := by
  refine ⟨List.getElem?_eq_none h,?_⟩
  intro i hi
  change l[i.val+1]?=none
  change l[i.val]?=none at hi
  exact List.getElem?_eq_none (by
    have := List.getElem?_eq_none_iff.mp hi
    omega)
lemma listRow_cell (L : ℕ) (l : List A) (h : l.length≤L) (i : ℕ) :
    rowCell L (listRow L l) i=l[i]? := by
  unfold rowCell
  split_ifs with hi
  · rfl
  · exact (List.getElem?_eq_none (by omega)).symm

lemma list_eq_of_row (L : ℕ) (l m : List A) (hl : l.length≤L) (hm : m.length≤L)
    (h : ∀ i≤L, l[i]?=m[i]?) : l=m := by
  apply List.ext_getElem?
  intro i
  by_cases hi : i≤L
  · exact h i hi
  · rw [List.getElem?_eq_none (by omega),List.getElem?_eq_none (by omega)]

lemma stack_eq_of_cells (L : ℕ) (l m : List A) (hm : m.length≤L)
    (h : ∀ i≤L, l[i]?=m[i]?) : l=m := by
  have hl : l.length≤L := List.getElem?_eq_none_iff.mp ((h L le_rfl).trans (List.getElem?_eq_none hm))
  exact list_eq_of_row L l m hl hm h
end MetricKMedian.PCP.Tableau

end Inline_PCPTableauRows

end OAI
