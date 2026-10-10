import OAI.NumberTheory.TwoPoint.Circuits.CircuitAssignmentUpdates

namespace OAI

/-! Complete query blocks along a canonical DNF path. A prefix of a path is
enough for the switching encoding; the final Boolean answer is irrelevant. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

structure DNFQueryBlock (n : ℕ) where
  term : CubeTerm n
  queried : Finset (Fin n)
  answer : BooleanCube n

namespace DNFQueryBlock

def support {n : ℕ} : List (DNFQueryBlock n) → Finset (Fin n)
  | [] => ∅
  | b :: bs => b.queried ∪ support bs

def length {n : ℕ} : List (DNFQueryBlock n) → ℕ
  | [] => 0
  | b :: bs => b.queried.card + length bs

def image {n : ℕ} : PartialAssignment n → List (DNFQueryBlock n) → PartialAssignment n
  | ρ, [] => ρ
  | ρ, b :: bs => image (ρ.assign b.queried b.term.value) bs

end DNFQueryBlock

inductive CanonicalDNFWalk {n : ℕ} :
    List (CubeTerm n) → PartialAssignment n → List (DNFQueryBlock n) → Prop
  | nil (F ρ) : CanonicalDNFWalk F ρ []
  | skip {C F ρ bs} (hC : ¬ C.Compatible ρ) (h : CanonicalDNFWalk F ρ bs) :
      CanonicalDNFWalk (C :: F) ρ bs
  | step {C F ρ bs} (x : BooleanCube n) (hC : C.Compatible ρ)
      (hne : (C.live ρ).Nonempty) (h : CanonicalDNFWalk F (ρ.assign (C.live ρ) x) bs) :
      CanonicalDNFWalk (C :: F) ρ (⟨C, C.live ρ, x⟩ :: bs)

namespace CanonicalDNFWalk

lemma support_subset_free {n : ℕ} {F : List (CubeTerm n)} {ρ : PartialAssignment n}
    {bs : List (DNFQueryBlock n)} (h : CanonicalDNFWalk F ρ bs) :
    DNFQueryBlock.support bs ⊆ ρ.free := by
  induction h with
  | nil => simp [DNFQueryBlock.support]
  | skip _ _ ih => exact ih
  | @step C F ρ bs x _ _ _ ih =>
    intro i hi
    rcases mem_union.mp hi with hi | hi
    · exact C.live_subset_free ρ hi
    · have hh := ih hi
      rw [PartialAssignment.free_assign] at hh
      exact (mem_sdiff.mp hh).1

lemma head_disjoint_tail {n : ℕ} {C : CubeTerm n} {F : List (CubeTerm n)}
    {ρ : PartialAssignment n} {bs : List (DNFQueryBlock n)} (x : BooleanCube n)
    (h : CanonicalDNFWalk F (ρ.assign (C.live ρ) x) bs) :
    Disjoint (C.live ρ) (DNFQueryBlock.support bs) := by
  apply Finset.disjoint_left.mpr
  intro i hi htail
  have hh := h.support_subset_free htail
  rw [PartialAssignment.free_assign] at hh
  exact (mem_sdiff.mp hh).2 hi

lemma length_eq_card_support {n : ℕ} {F : List (CubeTerm n)}
    {ρ : PartialAssignment n} {bs : List (DNFQueryBlock n)}
    (h : CanonicalDNFWalk F ρ bs) :
    DNFQueryBlock.length bs = (DNFQueryBlock.support bs).card := by
  induction h with
  | nil => simp [DNFQueryBlock.length, DNFQueryBlock.support]
  | skip _ _ ih => exact ih
  | @step C F ρ bs x _ _ h ih =>
    simp only [DNFQueryBlock.length, DNFQueryBlock.support]
    rw [card_union_of_disjoint (head_disjoint_tail x h), ih]

lemma length_le_dimension {n : ℕ} {F : List (CubeTerm n)}
    {ρ : PartialAssignment n} {bs : List (DNFQueryBlock n)}
    (h : CanonicalDNFWalk F ρ bs) : DNFQueryBlock.length bs ≤ n := by
  rw [h.length_eq_card_support]
  exact (card_le_card (subset_univ _)).trans_eq (by simp)

end CanonicalDNFWalk

end TwoPointCorrelations

end OAI
