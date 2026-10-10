import OAI.NumberTheory.Ostmann.Arithmetic.MovingSlotOccurrences
import OAI.NumberTheory.Ostmann.Arithmetic.MovingGiantSamples

namespace OAI

/-! # Labelled four-slot samples and the concrete occurrence paths -/

namespace Ostmann
open scoped Classical

/-- The same sampler as `MovingGiantSamples`, before the prime labels have
been evaluated. Four actual positions are used at each child leaf. -/
inductive MovingSampleSlots (σ : Type*) : ℕ → Type _
  | leaf : MovingSampleSlots σ 0
  | node {n : ℕ} (samples : TreeLeafTuple (Fin 4 → σ) n)
      (left right : MovingSampleSlots σ n) : MovingSampleSlots σ (n + 1)

def movingCompensationSlots {σ : Type*} : (n : ℕ) →
    TreeLeafTuple (Fin 4 → σ) n → TreeLeafTuple (List σ) n
  | 0, x => List.ofFn (show Fin 4 → σ from x)
  | n + 1, x => (movingCompensationSlots n x.1, movingCompensationSlots n x.2)

def flattenMovingSlots {σ : Type*} : (n : ℕ) → TreeLeafTuple (List σ) n → List σ
  | 0, x => (show List σ from x)
  | n + 1, x => flattenMovingSlots n x.1 ++ flattenMovingSlots n x.2

def appendMovingSlotLeaves {σ : Type*} : (n : ℕ) →
    TreeLeafTuple (List σ) n → TreeLeafTuple (List σ) n → TreeLeafTuple (List σ) n
  | 0, x, y => (show List σ from x) ++ (show List σ from y)
  | n + 1, x, y => (appendMovingSlotLeaves n x.1 y.1, appendMovingSlotLeaves n x.2 y.2)

theorem flattenMovingSlots_append_bound {σ : Type*} (tier : σ → ℕ) (r n : ℕ)
    (x y : TreeLeafTuple (List σ) n)
    (hx : ∀ i ∈ flattenMovingSlots n x, r ≤ tier i)
    (hy : ∀ i ∈ flattenMovingSlots n y, r ≤ tier i) :
    ∀ i ∈ flattenMovingSlots n (appendMovingSlotLeaves n x y), r ≤ tier i := by
  induction n with
  | zero =>
    intro i hi
    exact (List.mem_append.mp hi).elim (hx i) (hy i)
  | succ n ih =>
    intro i hi
    rcases List.mem_append.mp hi with hi | hi
    · exact ih x.1 y.1 (fun i h => hx i (List.mem_append_left _ h))
        (fun i h => hy i (List.mem_append_left _ h)) i hi
    · exact ih x.2 y.2 (fun i h => hx i (List.mem_append_right _ h))
        (fun i h => hy i (List.mem_append_right _ h)) i hi

def MovingSampleSlots.Levels {σ : Type*} (tier : σ → ℕ) :
    {n : ℕ} → MovingSampleSlots σ n → Prop
  | _, .leaf => True
  | n + 1, .node samples left right =>
      (∀ i ∈ flattenMovingSlots n (movingCompensationSlots n samples), tier i = n) ∧
      left.Levels tier ∧ right.Levels tier

/-- This carries the source's compensation product into both child regular
lists while retaining the per-leaf distribution of the four samples. -/
def buildMovingSlotData {σ : Type*} : (n : ℕ) → FrequencyTree ℤ n →
    TreeLeafTuple (List σ) n → TreeLeafTuple (List σ) n →
    MovingSampleSlots σ n → MovingSlotData σ n
  | 0, t, small, bulk, .leaf =>
      .leaf (frequencyRoot 0 t) (flattenMovingSlots 0 small ++ flattenMovingSlots 0 bulk)
  | n + 1, t, small, bulk, .node samples left right =>
      let u := movingCompensationSlots n samples
      .node t.1
        (flattenMovingSlots n small.1 ++ flattenMovingSlots n bulk.1)
        (flattenMovingSlots n small.2 ++ flattenMovingSlots n bulk.2)
        (flattenMovingSlots n u)
        (buildMovingSlotData n t.2.1 (appendMovingSlotLeaves n u small.1) bulk.1 left)
        (buildMovingSlotData n t.2.2 (appendMovingSlotLeaves n u small.2) bulk.2 right)

theorem buildMovingSlotData_levels {σ : Type*} (tier : σ → ℕ) (n : ℕ)
    (t : FrequencyTree ℤ n) (small bulk : TreeLeafTuple (List σ) n)
    (samples : MovingSampleSlots σ n)
    (hsmall : ∀ i ∈ flattenMovingSlots n small, n ≤ tier i)
    (hbulk : ∀ i ∈ flattenMovingSlots n bulk, n ≤ tier i)
    (hsamples : samples.Levels tier) :
    (buildMovingSlotData n t small bulk samples).Levels tier := by
  induction samples with
  | leaf => trivial
  | @node n samples left right ihL ihR =>
    have hsmallL : ∀ i ∈ flattenMovingSlots n small.1, n + 1 ≤ tier i :=
      fun i hi => hsmall i (List.mem_append_left _ hi)
    have hsmallR : ∀ i ∈ flattenMovingSlots n small.2, n + 1 ≤ tier i :=
      fun i hi => hsmall i (List.mem_append_right _ hi)
    have hbulkL : ∀ i ∈ flattenMovingSlots n bulk.1, n + 1 ≤ tier i :=
      fun i hi => hbulk i (List.mem_append_left _ hi)
    have hbulkR : ∀ i ∈ flattenMovingSlots n bulk.2, n + 1 ≤ tier i :=
      fun i hi => hbulk i (List.mem_append_right _ hi)
    refine ⟨?_, ?_, hsamples.1, ?_, ?_⟩
    · intro i hi
      exact (List.mem_append.mp hi).elim (hsmallL i) (hbulkL i)
    · intro i hi
      exact (List.mem_append.mp hi).elim (hsmallR i) (hbulkR i)
    · apply ihL _ _ _ _ _ hsamples.2.1
      · apply flattenMovingSlots_append_bound
        · intro i hi
          exact le_of_eq (hsamples.1 i hi).symm
        · intro i hi
          exact (Nat.le_succ n).trans (hsmallL i hi)
      · intro i hi
        exact (Nat.le_succ n).trans (hbulkL i hi)
    · apply ihR _ _ _ _ _ hsamples.2.2
      · apply flattenMovingSlots_append_bound
        · intro i hi
          exact le_of_eq (hsamples.1 i hi).symm
        · intro i hi
          exact (Nat.le_succ n).trans (hsmallR i hi)
      · intro i hi
        exact (Nat.le_succ n).trans (hbulkR i hi)

/-- Omission is now a proved fact of the actual sample constructor. -/
theorem buildMovingSlotData_occurrence_absent {σ : Type*} (tier : σ → ℕ) (n : ℕ)
    (t : FrequencyTree ℤ n) (small bulk : TreeLeafTuple (List σ) n)
    (samples : MovingSampleSlots σ n)
    (hsmall : ∀ i ∈ flattenMovingSlots n small, n ≤ tier i)
    (hbulk : ∀ i ∈ flattenMovingSlots n bulk, n ≤ tier i)
    (hsamples : samples.Levels tier) (o : MovingSlotOccurrence σ)
    (ho : o ∈ (buildMovingSlotData n t small bulk samples).occurrences)
    (i : σ) (hi : tier i < o.level) :
    (∀ s ∈ o.path, i ∉ s.leftSlots ∧ i ∉ s.rightSlots ∧ i ∉ s.compensationSlots) ∧
      i ∉ o.current.leftSlots ∧ i ∉ o.current.rightSlots := by
  have h := MovingSlotData.occurrence_bounds tier _
    (buildMovingSlotData_levels tier n t small bulk samples hsmall hbulk hsamples) o ho
  exact o.absent_of_level tier h.2.2 i hi

end Ostmann

end OAI
