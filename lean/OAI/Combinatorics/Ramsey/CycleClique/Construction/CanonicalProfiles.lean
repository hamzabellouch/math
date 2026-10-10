import OAI.Combinatorics.Ramsey.CycleClique.Construction.PathProfiles
import Mathlib.Data.List.Sort

namespace OAI

/-! Every actual path system has a representative in the finite canonical
amount domain: reverse components into lexicographic order, then sort them. -/

namespace CycleClique.Construction
theorem lexLE_iff_le (a b : List ℕ) : LexLE a b ↔ a ≤ b := by
  change (a = b ∨ a < b) ↔ a ≤ b
  exact le_iff_eq_or_lt.symm

def orientAmounts (p : List ℕ) : List ℕ := if p ≤ p.reverse then p else p.reverse

def canonicalAmounts (P : List (List ℕ)) : List (List ℕ) :=
  (P.map orientAmounts).mergeSort (fun a b => decide (a ≤ b))

theorem orientAmounts_length (p : List ℕ) : (orientAmounts p).length = p.length := by
  unfold orientAmounts
  split_ifs <;> simp

theorem orientAmounts_sum (p : List ℕ) : (orientAmounts p).sum = p.sum := by
  unfold orientAmounts
  split_ifs <;> simp

theorem orientAmounts_reverse (p : List ℕ) :
    LexLE (orientAmounts p) (orientAmounts p).reverse := by
  rw [lexLE_iff_le]
  unfold orientAmounts
  split_ifs with hp
  · exact hp
  · simpa only [List.reverse_reverse] using (lt_of_not_ge hp).le

theorem orientAmounts_positive {p : List ℕ} (hp : ∀ a ∈ p, 0 < a) :
    ∀ a ∈ orientAmounts p, 0 < a := by
  unfold orientAmounts
  split_ifs
  · exact hp
  · intro a ha
    exact hp a (List.mem_reverse.mp ha)

theorem canonicalAmounts_perm (P : List (List ℕ)) :
    (canonicalAmounts P).Perm (P.map orientAmounts) := List.mergeSort_perm _ _

theorem canonicalAmounts_vertices (P : List (List ℕ)) :
    patternVertices (canonicalAmounts P) = patternVertices P := by
  unfold patternVertices
  rw [((canonicalAmounts_perm P).map (fun p => p.length + 1)).sum_eq]
  simp only [List.map_map, Function.comp_def, orientAmounts_length]

theorem canonicalAmounts_amount (P : List (List ℕ)) :
    patternAmount (canonicalAmounts P) = patternAmount P := by
  unfold patternAmount
  rw [((canonicalAmounts_perm P).map List.sum).sum_eq]
  simp only [List.map_map, Function.comp_def, orientAmounts_sum]

theorem canonicalAmounts_pairwise (P : List (List ℕ)) :
    (canonicalAmounts P).Pairwise LexLE := by
  have hp := List.pairwise_mergeSort (le := fun a b : List ℕ => decide (a ≤ b))
    (fun a b c hab hbc => by simpa using le_trans (of_decide_eq_true hab) (of_decide_eq_true hbc))
    (fun a b => by simpa using le_total a b) (P.map orientAmounts)
  apply hp.imp
  intro a b hab
  exact (lexLE_iff_le a b).mpr (of_decide_eq_true hab)

theorem patternValid_of_pairwise {P : List (List ℕ)}
    (hsorted : P.Pairwise LexLE)
    (horient : ∀ p ∈ P, LexLE p p.reverse)
    (hpos : ∀ p ∈ P, ∀ a ∈ p, 0 < a)
    {first : List ℕ} (hfirst : ∀ p ∈ P, LexLE first p) : PatternValid first P := by
  induction P generalizing first with
  | nil => trivial
  | cons p P ih =>
    obtain ⟨hhead, htail⟩ := List.pairwise_cons.mp hsorted
    exact ⟨hfirst p (by simp), horient p (by simp), hpos p (by simp),
      ih htail (fun p hp => horient p (by simp [hp]))
        (fun p hp => hpos p (by simp [hp])) hhead⟩

theorem canonicalAmounts_valid {P : List (List ℕ)}
    (hpos : ∀ p ∈ P, ∀ a ∈ p, 0 < a) : PatternValid [] (canonicalAmounts P) := by
  apply patternValid_of_pairwise (canonicalAmounts_pairwise P)
  · intro p hp
    obtain ⟨q, _, rfl⟩ := List.mem_map.mp ((canonicalAmounts_perm P).mem_iff.mp hp)
    exact orientAmounts_reverse q
  · intro p hp
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp ((canonicalAmounts_perm P).mem_iff.mp hp)
    exact orientAmounts_positive (hpos q hq)
  · intro p hp
    rw [lexLE_iff_le]
    cases p with
    | nil => exact le_rfl
    | cons a p => exact le_of_lt List.Lex.nil

theorem canonicalAmounts_mem {P : List (List ℕ)} {t b : ℕ}
    (hvertices : patternVertices P = t) (hamount : patternAmount P ≤ b)
    (hpos : ∀ p ∈ P, ∀ a ∈ p, 0 < a) :
    canonicalAmounts P ∈ pathPatterns t b := by
  apply mem_pathPatterns.mpr
  rw [canonicalAmounts_vertices, canonicalAmounts_amount]
  exact ⟨hvertices, hamount, canonicalAmounts_valid hpos⟩

namespace ExpandedPathSystem

variable {V : Type*} {G : SimpleGraph V} {Q : Finset V}

theorem exists_canonical_profile (S : ExpandedPathSystem G Q) {b : ℕ}
    (hbudget : S.amount ≤ b) :
    ∃ P : List (List ℕ),
      List.Forall₂ (AssignedAmounts Q) S.toRaw.completeClique.chains P ∧
      canonicalAmounts P ∈ pathPatterns Q.card b := by
  obtain ⟨P, hp, hv, ha, _, hpos⟩ := S.exists_complete_profile
  exact ⟨P, hp, canonicalAmounts_mem hv (by omega) hpos⟩

end ExpandedPathSystem

end CycleClique.Construction

end OAI
