import OAI.NumberTheory.Ostmann.Arithmetic.MovingRepresentativeLineSystem
import OAI.NumberTheory.Ostmann.Arithmetic.MovingSampleSizes

namespace OAI

/-! # A fixed finite index for every representative's actual line system -/

namespace Ostmann
open scoped Classical BigOperators

abbrev MovingPairOccurrenceIndex {σ : Type*} {n : ℕ}
    (T : Bool → MovingSlotData σ n) := Σ side : Bool, Fin (T side).occurrences.length

theorem movingPairOccurrenceIndex_card {σ : Type*} {n : ℕ}
    (T : Bool → MovingSlotData σ n) :
    Fintype.card (MovingPairOccurrenceIndex T) = 2 * (2 ^ n - 1) := by
  simp only [MovingPairOccurrenceIndex, Fintype.card_sigma, Fintype.card_fin,
    Fintype.sum_bool, MovingSlotData.occurrences_length]
  omega

/-- Indices outside a representative's system repeat its selected base row.
Thus every representative uses the same finite index without changing any test. -/
noncomputable def movingRepresentativeIndex {σ : Type*} {n : ℕ}
    (T : Bool → MovingSlotData σ n) (rep : σ) (base : MovingPairRepresentativeOccurrences T rep)
    (o : MovingPairOccurrenceIndex T) : MovingPairRepresentativeOccurrences T rep :=
  if h : rep ∈ ((T o.1).occurrences.get o.2).current.compensationSlots then
    ⟨o.1, ⟨o.2, h⟩⟩ else base

theorem movingRepresentativeIndex_surjective {σ : Type*} {n : ℕ}
    (T : Bool → MovingSlotData σ n) (rep : σ) (base : MovingPairRepresentativeOccurrences T rep) :
    Function.Surjective (movingRepresentativeIndex T rep base) := by
  intro j
  refine ⟨⟨j.1, j.2.val⟩, ?_⟩
  simp only [movingRepresentativeIndex, dite_eq_left j.2.property]

noncomputable def movingIndexedOccurrence {σ : Type*} {n : ℕ}
    (T : Bool → MovingSlotData σ n) (rep : σ) (base : MovingPairRepresentativeOccurrences T rep)
    (o : MovingPairOccurrenceIndex T) : MovingSlotOccurrence σ :=
  let j := movingRepresentativeIndex T rep base o
  (T j.1).occurrences.get j.2.val

noncomputable def movingIndexedLine {σ : Type*} {n : ℕ}
    (T : Bool → MovingSlotData σ n) (rep : σ) (base : MovingPairRepresentativeOccurrences T rep)
    (o : MovingPairOccurrenceIndex T) : PolynomialGiantLine σ :=
  movingSlotLine (movingIndexedOccurrence T rep base o).path
    (movingIndexedOccurrence T rep base o).current

theorem movingIndexedOccurrence_absent {σ : Type*} {n : ℕ}
    (T : Bool → MovingSlotData σ n) (tier : σ → ℕ) (hlevels : ∀ side, (T side).Levels tier)
    (rep : σ) (base : MovingPairRepresentativeOccurrences T rep) (o : MovingPairOccurrenceIndex T) :
    (∀ s ∈ (movingIndexedOccurrence T rep base o).path,
      rep ∉ s.leftSlots ∧ rep ∉ s.rightSlots ∧ rep ∉ s.compensationSlots) ∧
      rep ∉ (movingIndexedOccurrence T rep base o).current.leftSlots ∧
      rep ∉ (movingIndexedOccurrence T rep base o).current.rightSlots := by
  let j := movingRepresentativeIndex T rep base o
  let t := (T j.1).occurrences.get j.2.val
  have ht : t ∈ (T j.1).occurrences := List.get_mem _ _
  have hbound := (T j.1).occurrence_bounds tier (hlevels j.1) t ht
  have hrep := (T j.1).occurrence_compensation_level tier (hlevels j.1) t ht rep j.2.property
  exact t.absent_of_level tier hbound.2.2 rep hrep

theorem movingIndexedOccurrence_path_length {σ : Type*} {n : ℕ}
    (T : Bool → MovingSlotData σ n) (tier : σ → ℕ) (hlevels : ∀ side, (T side).Levels tier)
    (rep : σ) (base : MovingPairRepresentativeOccurrences T rep) (o : MovingPairOccurrenceIndex T) :
    (movingIndexedOccurrence T rep base o).path.length ≤ n := by
  let j := movingRepresentativeIndex T rep base o
  have h := (T j.1).occurrence_bounds tier (hlevels j.1)
    ((T j.1).occurrences.get j.2.val) (List.get_mem _ _)
  exact (Nat.le_add_left _ _).trans h.2.1

theorem movingIndexedOccurrence_units {σ : Type*} {n : ℕ}
    (T : Bool → MovingSlotData σ n) (tier : σ → ℕ) (value : σ → ℕ)
    (hprime : ∀ i, (value i).Prime)
    (hdisjoint : ∀ i j, tier i ≠ tier j → value i ≠ value j)
    (hlevels : ∀ side, (T side).Levels tier)
    (rep : σ) (base : MovingPairRepresentativeOccurrences T rep)
    (hf : ∀ side, (T side).Frequencies (fun s => (s : ZMod (value rep)) ≠ 0))
    (o : MovingPairOccurrenceIndex T) :
    let φ := MovingSlotReversal.naturalReduction (value rep) value
    let t := movingIndexedOccurrence T rep base o
    (∀ s ∈ t.path, φ s.polynomial.v ≠ 0 ∧ φ s.polynomial.w ≠ 0 ∧ φ s.polynomial.u ≠ 0) ∧
      φ t.current.polynomial.v ≠ 0 ∧ φ t.current.polynomial.w ≠ 0 := by
  let j := movingRepresentativeIndex T rep base o
  let t := (T j.1).occurrences.get j.2.val
  have ht : t ∈ (T j.1).occurrences := List.get_mem _ _
  exact (T j.1).occurrence_units_of_prime_types tier value hprime hdisjoint (hlevels j.1)
    t ht rep ((T j.1).occurrence_compensation_level tier (hlevels j.1) t ht rep j.2.property)
    (hf j.1)

theorem movingIndexedOccurrence_size {σ : Type*} {n : ℕ}
    (T : Bool → MovingSlotData σ n) (d : ℕ) (F : ℝ)
    (hsize : ∀ side, (T side).SizeLE d)
    (hfreq : ∀ side, (T side).Frequencies (fun s => |(s : ℝ)| ≤ F))
    (rep : σ) (base : MovingPairRepresentativeOccurrences T rep) (o : MovingPairOccurrenceIndex T) :
    (∀ s ∈ (movingIndexedOccurrence T rep base o).path, s.lengthLE d ∧ s.frequencyLE F) ∧
      (movingIndexedOccurrence T rep base o).current.lengthLE d ∧
      (movingIndexedOccurrence T rep base o).current.frequencyLE F := by
  let j := movingRepresentativeIndex T rep base o
  let t := (T j.1).occurrences.get j.2.val
  have ht : t ∈ (T j.1).occurrences := List.get_mem _ _
  have hs := (T j.1).occurrence_size (hsize j.1) t ht
  have hf := (T j.1).occurrence_frequencies _ (hfreq j.1) t ht
  exact ⟨fun s h => ⟨hs.2 s h, hf.2 s h⟩, hs.1, hf.1⟩

theorem movingInternalBaseProbability_indexed {σ : Type*} {n : ℕ}
    (value : σ → ℕ) (T : Bool → MovingSlotData σ n) (rep : σ)
    [Fact (value rep).Prime] (hunique : ∀ i, value i = value rep → i = rep)
    (base : MovingPairRepresentativeOccurrences T rep) :
    internalLineProbability true
      (fun j => MovingSlotReversal.naturalReduction (value rep) value
        (movingPrimeOccurrenceLine value T (value rep) j).a)
      (fun j => MovingSlotReversal.naturalReduction (value rep) value
        (movingPrimeOccurrenceLine value T (value rep) j).b) =
    internalLineProbability true
      (fun j => MovingSlotReversal.naturalReduction (value rep) value
        (movingIndexedLine T rep base j).a)
      (fun j => MovingSlotReversal.naturalReduction (value rep) value
        (movingIndexedLine T rep base j).b) := by
  rw [movingInternalBaseProbability_representative value T rep hunique]
  have he (x y : ZMod (value rep)) :
      (∀ j : MovingPairRepresentativeOccurrences T rep,
        let φ := MovingSlotReversal.naturalReduction (value rep) value
        let L := movingRepresentativeLine T rep j
        φ L.a * x + φ L.b * y = 0) ↔
      (∀ o : MovingPairOccurrenceIndex T,
        let φ := MovingSlotReversal.naturalReduction (value rep) value
        let L := movingIndexedLine T rep base o
        φ L.a * x + φ L.b * y = 0) :=
    (movingRepresentativeIndex_surjective T rep base).forall
  unfold internalLineProbability
  simp only [ite_true, ← Nat.card_eq_fintype_card]
  apply congrArg (fun k : ℕ => (k : ℝ) / Nat.card (ZMod (value rep) × (ZMod (value rep))ˣ))
  exact Nat.card_congr (Equiv.subtypeEquivRight
    (fun z : ZMod (value rep) × (ZMod (value rep))ˣ => he z.1 z.2))

end Ostmann

end OAI
