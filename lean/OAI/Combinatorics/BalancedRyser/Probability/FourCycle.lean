import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Fin
import Mathlib.Tactic.FinCases

namespace OAI

namespace Balanced.FourCycle

def opposite (i : Fin 4) : Fin 4 := i + 2

def SameBlock (i j : Fin 4) : Prop := i.val % 2 = j.val % 2

def Consecutive (i j : Fin 4) : Prop := j = i + 1 ∨ i = j + 1

theorem opposite_ne (i : Fin 4) : opposite i ≠ i := by
  fin_cases i <;> decide

theorem opposite_opposite (i : Fin 4) : opposite (opposite i) = i := by
  fin_cases i <;> decide

theorem sameBlock_iff (i j : Fin 4) :
    SameBlock i j ↔ j = i ∨ j = opposite i := by
  fin_cases i <;> fin_cases j <;> simp [SameBlock, opposite]

theorem not_sameBlock_iff_consecutive (i j : Fin 4) :
    ¬ SameBlock i j ↔ Consecutive i j := by
  fin_cases i <;> fin_cases j <;> simp [SameBlock, Consecutive]

theorem sameBlock_or_consecutive (i j : Fin 4) :
    SameBlock i j ∨ Consecutive i j := by
  fin_cases i <;> fin_cases j <;> simp [SameBlock, Consecutive]

variable {α : Type*}

def designated [DecidableEq α] (u : Fin 4 → α) : Finset α :=
  Finset.univ.image u

def evenBlock [DecidableEq α] (u : Fin 4 → α) : Finset α := {u 0, u 2}

def oddBlock [DecidableEq α] (u : Fin 4 → α) : Finset α := {u 1, u 3}

section Finsets
variable [DecidableEq α] (u : Fin 4 → α)

@[simp] theorem mem_designated (x : α) :
    x ∈ designated u ↔ ∃ i, u i = x := by
  simp [designated]

theorem point_mem_designated (i : Fin 4) : u i ∈ designated u := by
  exact (mem_designated u (u i)).2 ⟨i, rfl⟩

theorem card_designated (hu : Function.Injective u) : (designated u).card = 4 := by
  rw [designated, Finset.card_image_of_injective _ hu]
  simp

theorem even_union_odd : evenBlock u ∪ oddBlock u = designated u := by
  ext x
  simp only [evenBlock, oddBlock, Finset.mem_union, Finset.mem_insert,
    Finset.mem_singleton, mem_designated]
  constructor
  · rintro ((h | h) | (h | h))
    · exact ⟨0, h.symm⟩
    · exact ⟨2, h.symm⟩
    · exact ⟨1, h.symm⟩
    · exact ⟨3, h.symm⟩
  · rintro ⟨i, rfl⟩
    fin_cases i <;> simp

theorem even_odd_disjoint (hu : Function.Injective u) :
    Disjoint (evenBlock u) (oddBlock u) := by
  apply Finset.disjoint_left.mpr
  intro x hx hy
  simp only [evenBlock, oddBlock, Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with hx | hx <;> rcases hy with hy | hy
  all_goals have h := hu (hx.symm.trans hy)
  all_goals contradiction

theorem card_evenBlock (hu : Function.Injective u) : (evenBlock u).card = 2 := by
  have h : u 0 ≠ u 2 := fun he => by have := hu he; contradiction
  simp [evenBlock, h]

theorem card_oddBlock (hu : Function.Injective u) : (oddBlock u).card = 2 := by
  have h : u 1 ≠ u 3 := fun he => by have := hu he; contradiction
  simp [oddBlock, h]

end Finsets

theorem adjacency_of_separated (u : Fin 4 → α) (Adj : α → α → Prop)
    (hsymm : ∀ x y, Adj x y → Adj y x)
    (hcycle : ∀ i : Fin 4, Adj (u i) (u (i + 1)))
    {i j : Fin 4} (h : ¬ SameBlock i j) : Adj (u i) (u j) := by
  rcases (not_sameBlock_iff_consecutive i j).1 h with h | h
  · simpa only [h] using hcycle i
  · rw [h]
    exact hsymm _ _ (hcycle j)

theorem opposite_uncovered (u : Fin 4 → α) (hu : Function.Injective u)
    (Adj : α → α → Prop) (hopp : ∀ i, ¬ Adj (u i) (u (opposite i)))
    (i : Fin 4) : u (opposite i) ≠ u i ∧ ¬ Adj (u i) (u (opposite i)) := by
  exact ⟨fun h => opposite_ne i (hu h), hopp i⟩

theorem exists_uncovered (u : Fin 4 → α) (hu : Function.Injective u)
    (Adj : α → α → Prop) (hopp : ∀ i, ¬ Adj (u i) (u (opposite i)))
    (p : α)
    (hexternal : (∀ i, u i ≠ p) →
      ∀ i j, Adj p (u i) → Adj p (u j) → i = j) :
    ∃ i, u i ≠ p ∧ ¬ Adj p (u i) := by
  classical
  by_cases hp : ∃ i, u i = p
  · obtain ⟨i, rfl⟩ := hp
    exact ⟨opposite i, opposite_uncovered u hu Adj hopp i⟩
  · have hp' : ∀ i, u i ≠ p := by simpa only [not_exists] using hp
    by_cases h0 : Adj p (u 0)
    · refine ⟨1, hp' 1, ?_⟩
      intro h1
      have h := hexternal hp' 0 1 h0 h1
      contradiction
    · exact ⟨0, hp' 0, h0⟩

theorem not_covered (u : Fin 4 → α) (hu : Function.Injective u)
    (Adj : α → α → Prop) (hopp : ∀ i, ¬ Adj (u i) (u (opposite i)))
    (p : α)
    (hexternal : (∀ i, u i ≠ p) →
      ∀ i j, Adj p (u i) → Adj p (u j) → i = j)
    (Covered : α → Prop)
    (htrace : ∀ i, Covered (u i) → u i = p ∨ Adj p (u i)) :
    ¬ ∀ i, Covered (u i) := by
  obtain ⟨i, hne, hnot⟩ := exists_uncovered u hu Adj hopp p hexternal
  intro hall
  exact (htrace i (hall i)).elim hne hnot

theorem sameBlock_pairs (i j : Fin 4) (h : SameBlock i j) :
    ((i = 0 ∨ i = 2) ∧ (j = 0 ∨ j = 2)) ∨
      ((i = 1 ∨ i = 3) ∧ (j = 1 ∨ j = 3)) := by
  fin_cases i <;> fin_cases j <;> simp_all [SameBlock]

theorem common_block_or_adjacent [DecidableEq α] (u : Fin 4 → α)
    (Adj : α → α → Prop) (hsymm : ∀ x y, Adj x y → Adj y x)
    (hcycle : ∀ i : Fin 4, Adj (u i) (u (i + 1)))
    {x y : α} (hx : x ∈ designated u) (hy : y ∈ designated u) :
    (x ∈ evenBlock u ∧ y ∈ evenBlock u) ∨
      (x ∈ oddBlock u ∧ y ∈ oddBlock u) ∨ Adj x y := by
  obtain ⟨i, rfl⟩ := (mem_designated u x).1 hx
  obtain ⟨j, rfl⟩ := (mem_designated u y).1 hy
  rcases sameBlock_or_consecutive i j with h | h
  · rcases sameBlock_pairs i j h with h | h
    · left
      simpa only [evenBlock, Finset.mem_insert, Finset.mem_singleton] using
        And.intro (h.1.imp (congrArg u) (congrArg u))
          (h.2.imp (congrArg u) (congrArg u))
    · right; left
      simpa only [oddBlock, Finset.mem_insert, Finset.mem_singleton] using
        And.intro (h.1.imp (congrArg u) (congrArg u))
          (h.2.imp (congrArg u) (congrArg u))
  · right; right
    exact adjacency_of_separated u Adj hsymm hcycle
      ((not_sameBlock_iff_consecutive i j).2 h)

theorem external_neighbors_card_le_one [DecidableEq α]
    (u : Fin 4 → α) (Adj : α → α → Prop) [DecidableRel Adj] (p : α)
    (hexternal : ∀ i j, Adj p (u i) → Adj p (u j) → i = j) :
    ((designated u).filter (Adj p)).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro x hx y hy
  obtain ⟨hx, hax⟩ := Finset.mem_filter.mp hx
  obtain ⟨hy, hay⟩ := Finset.mem_filter.mp hy
  obtain ⟨i, rfl⟩ := (mem_designated u x).1 hx
  obtain ⟨j, rfl⟩ := (mem_designated u y).1 hy
  exact congrArg u (hexternal i j hax hay)

end Balanced.FourCycle

end OAI
