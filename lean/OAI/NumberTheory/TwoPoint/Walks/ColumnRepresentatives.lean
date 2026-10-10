import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Fin
import Mathlib.Tactic

namespace OAI

/-! Canonical occurrence representatives for the imperfect-position code. -/

namespace TwoPointCorrelations

open Finset

variable {α : Type*} [DecidableEq α] {N : ℕ}

def columnRepresentativeCandidates (label : Fin N → α) (perfect : Finset (Fin N))
    (i : Fin N) : Finset (Fin N) :=
  let p := perfect.filter (fun j => label j = label i)
  if p.Nonempty then p else univ.filter (fun j => label j = label i)

lemma columnRepresentativeCandidates_nonempty (label : Fin N → α)
    (perfect : Finset (Fin N)) (i : Fin N) :
    (columnRepresentativeCandidates label perfect i).Nonempty := by
  dsimp only [columnRepresentativeCandidates]
  split_ifs with h
  · exact h
  · exact ⟨i, mem_filter.mpr ⟨mem_univ _, rfl⟩⟩

def columnRepresentative (label : Fin N → α) (perfect : Finset (Fin N)) (i : Fin N) : Fin N :=
  (columnRepresentativeCandidates label perfect i).min'
    (columnRepresentativeCandidates_nonempty label perfect i)

lemma columnRepresentative_mem (label : Fin N → α) (perfect : Finset (Fin N)) (i : Fin N) :
    columnRepresentative label perfect i ∈ columnRepresentativeCandidates label perfect i :=
  min'_mem _ _

/-- A reference always carries the intended label. -/
theorem columnRepresentative_label (label : Fin N → α) (perfect : Finset (Fin N)) (i : Fin N) :
    label (columnRepresentative label perfect i) = label i := by
  have hm := columnRepresentative_mem label perfect i
  dsimp only [columnRepresentativeCandidates] at hm
  split_ifs at hm <;> exact (mem_filter.mp hm).2

/-- Perfect occurrences are preferred whenever the class has one. -/
theorem columnRepresentative_perfect (label : Fin N → α) (perfect : Finset (Fin N)) (i : Fin N)
    (h : ∃ j ∈ perfect, label j = label i) : columnRepresentative label perfect i ∈ perfect := by
  have hp : (perfect.filter (fun j => label j = label i)).Nonempty := by
    obtain ⟨j, hj, heq⟩ := h
    exact ⟨j, mem_filter.mpr ⟨hj, heq⟩⟩
  have hm := columnRepresentative_mem label perfect i
  simp only [columnRepresentativeCandidates, hp, ite_true] at hm
  exact (mem_filter.mp hm).1

/-- An unrepresented class refers to its first occurrence, which is
necessarily imperfect; two such classes cannot share a reference. -/
theorem columnRepresentative_imperfect (label : Fin N → α) (perfect : Finset (Fin N)) (i : Fin N)
    (h : ¬∃ j ∈ perfect, label j = label i) : columnRepresentative label perfect i ∉ perfect := by
  intro hm
  exact h ⟨_, hm, columnRepresentative_label label perfect i⟩

theorem columnRepresentative_eq_iff (label : Fin N → α) (perfect : Finset (Fin N))
    (i j : Fin N) : columnRepresentative label perfect i = columnRepresentative label perfect j ↔
      label i = label j := by
  constructor
  · intro h
    exact (columnRepresentative_label label perfect i).symm.trans
      ((congrArg label h).trans (columnRepresentative_label label perfect j))
  · intro h
    have hc : columnRepresentativeCandidates label perfect i =
        columnRepresentativeCandidates label perfect j := by
      simp only [columnRepresentativeCandidates, h]
    unfold columnRepresentative
    simp only [hc]

/-- In the absence of a perfect representative, the selected occurrence
precedes every other occurrence in its class. -/
theorem columnRepresentative_first (label : Fin N → α) (perfect : Finset (Fin N)) (i : Fin N)
    (h : ¬∃ j ∈ perfect, label j = label i) (j : Fin N) (hj : label j = label i) :
    columnRepresentative label perfect i ≤ j := by
  apply min'_le
  have hp : ¬(perfect.filter (fun j => label j = label i)).Nonempty := by
    rintro ⟨k, hk⟩
    exact h ⟨k, (mem_filter.mp hk).1, (mem_filter.mp hk).2⟩
  simp only [columnRepresentativeCandidates, hp, ite_false]
  exact mem_filter.mpr ⟨mem_univ _, hj⟩

end TwoPointCorrelations

end OAI
