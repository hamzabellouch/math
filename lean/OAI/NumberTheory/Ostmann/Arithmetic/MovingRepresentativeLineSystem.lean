import OAI.NumberTheory.Ostmann.Arithmetic.MovingInternalBaseAverage

namespace OAI

/-! # Fixed occurrence systems for a representative sampled prime -/

namespace Ostmann
open scoped Classical BigOperators

abbrev MovingPairRepresentativeOccurrences {σ : Type*} {n : ℕ}
    (T : Bool → MovingSlotData σ n) (rep : σ) :=
  Σ side : Bool, MovingRepresentativeOccurrences (T side) rep

noncomputable def movingRepresentativeLine {σ : Type*} {n : ℕ}
    (T : Bool → MovingSlotData σ n) (rep : σ)
    (j : MovingPairRepresentativeOccurrences T rep) : PolynomialGiantLine σ :=
  let o := (T j.1).occurrences.get j.2.val
  movingSlotLine o.path o.current

/-- On samples with distinct prime values, all occurrences of the selected
prime are precisely the fixed occurrences of its representative slot. -/
theorem movingPrimeLineSystem_representative_iff {σ : Type*} {n : ℕ}
    (value : σ → ℕ) (T : Bool → MovingSlotData σ n) (rep : σ)
    (hunique : ∀ i, value i = value rep → i = rep)
    (x y : ZMod (value rep)) :
    (∀ j : MovingPrimeOccurrences value T (value rep),
      let φ := MovingSlotReversal.naturalReduction (value rep) value
      let L := movingPrimeOccurrenceLine value T (value rep) j
      φ L.a * x + φ L.b * y = 0) ↔
    (∀ j : MovingPairRepresentativeOccurrences T rep,
      let φ := MovingSlotReversal.naturalReduction (value rep) value
      let L := movingRepresentativeLine T rep j
      φ L.a * x + φ L.b * y = 0) := by
  constructor
  · intro h j
    let k : MovingPrimeOccurrences value T (value rep) :=
      ⟨j.1, ⟨j.2.val, ⟨rep, j.2.property, rfl⟩⟩⟩
    exact h k
  · intro h j
    obtain ⟨i, hi, hv⟩ := j.2.property
    have he : i = rep := hunique i hv
    subst i
    let k : MovingPairRepresentativeOccurrences T rep := ⟨j.1, ⟨j.2.val, hi⟩⟩
    exact h k

/-- This reindexing fixes the polynomial family before the prime values are
sampled, as required by the joint small-prime coincidence theorem. -/
theorem movingInternalBaseProbability_representative {σ : Type*} {n : ℕ}
    (value : σ → ℕ) (T : Bool → MovingSlotData σ n) (rep : σ)
    [Fact (value rep).Prime] (hunique : ∀ i, value i = value rep → i = rep) :
    internalLineProbability true
      (fun j => MovingSlotReversal.naturalReduction (value rep) value
        (movingPrimeOccurrenceLine value T (value rep) j).a)
      (fun j => MovingSlotReversal.naturalReduction (value rep) value
        (movingPrimeOccurrenceLine value T (value rep) j).b) =
    internalLineProbability true
      (fun j => MovingSlotReversal.naturalReduction (value rep) value
        (movingRepresentativeLine T rep j).a)
      (fun j => MovingSlotReversal.naturalReduction (value rep) value
        (movingRepresentativeLine T rep j).b) := by
  unfold internalLineProbability
  simp only [ite_true, ← Nat.card_eq_fintype_card]
  apply congrArg (fun k : ℕ => (k : ℝ) / Nat.card (ZMod (value rep) × (ZMod (value rep))ˣ))
  exact Nat.card_congr (Equiv.subtypeEquivRight
    (fun z : ZMod (value rep) × (ZMod (value rep))ˣ =>
      movingPrimeLineSystem_representative_iff value T rep hunique z.1 z.2))

end Ostmann

end OAI
