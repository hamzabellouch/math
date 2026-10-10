import OAI.NumberTheory.Ostmann.Arithmetic.MovingInternalLocalFactor
import OAI.NumberTheory.Ostmann.Arithmetic.MovingRepresentativeSquares

namespace OAI

/-! # Simultaneous occurrences of one actual internal prime in both histories -/

namespace Ostmann
open scoped Classical BigOperators

abbrev MovingPrimeOccurrences {σ : Type*} {n : ℕ}
    (value : σ → ℕ) (T : Bool → MovingSlotData σ n) (p : ℕ) :=
  Σ side : Bool, {j : Fin (T side).occurrences.length //
    ∃ i ∈ ((T side).occurrences.get j).current.compensationSlots, value i = p}

def movingPrimeOccurrence {σ : Type*} {n : ℕ}
    (value : σ → ℕ) (T : Bool → MovingSlotData σ n) (p : ℕ)
    (j : MovingPrimeOccurrences value T p) : MovingSlotOccurrence σ :=
  (T j.1).occurrences.get j.2.val

noncomputable def movingPrimeOccurrenceLine {σ : Type*} {n : ℕ}
    (value : σ → ℕ) (T : Bool → MovingSlotData σ n) (p : ℕ)
    (j : MovingPrimeOccurrences value T p) : PolynomialGiantLine σ :=
  let o := movingPrimeOccurrence value T p j
  movingSlotLine o.path o.current

theorem movingPrimeOccurrences_card {σ : Type*} {n : ℕ}
    (value : σ → ℕ) (T : Bool → MovingSlotData σ n) (p : ℕ) :
    Fintype.card (MovingPrimeOccurrences value T p) ≤ 2 * (2 ^ n - 1) := by
  have h (side : Bool) : Fintype.card {j : Fin (T side).occurrences.length //
      ∃ i ∈ ((T side).occurrences.get j).current.compensationSlots, value i = p} ≤ 2 ^ n - 1 := by
    calc
      _ ≤ Fintype.card (Fin (T side).occurrences.length) :=
        Fintype.card_le_of_injective Subtype.val Subtype.val_injective
      _ = _ := by rw [Fintype.card_fin, MovingSlotData.occurrences_length]
  rw [Fintype.card_sigma, Fintype.sum_bool]
  have h0 := h false
  have h1 := h true
  omega

theorem movingInternalLocalSupport_occurrences {σ : Type*} {n : ℕ}
    (value : σ → ℕ) (T : Bool → MovingSlotData σ n) (p : ℕ)
    (x y : ZMod (p ^ 2)) :
    (∀ side, movingInternalLocalSupport value (T side) p x y) ↔
      ∀ j : MovingPrimeOccurrences value T p,
        let L := movingPrimeOccurrenceLine value T p j
        let φ := MovingSlotReversal.naturalReduction (p ^ 2) value
        squareReduction p (φ L.a * x + φ L.b * y) = 0 ∧ φ L.a * x + φ L.b * y ≠ 0 := by
  constructor
  · intro h j
    obtain ⟨i, hi, hpi⟩ := j.2.property
    exact h j.1 _ (List.get_mem _ _) i hi hpi
  · intro h side o ho i hi hpi
    obtain ⟨k, hk, hko⟩ := List.mem_iff_getElem.mp ho
    let j : MovingPrimeOccurrences value T p :=
      ⟨side, ⟨⟨k, hk⟩, by simpa only [List.get_eq_getElem, hko] using ⟨i, hi, hpi⟩⟩⟩
    simpa only [movingPrimeOccurrenceLine, movingPrimeOccurrence, j, List.get_eq_getElem, hko] using h j

/-- Every row used by the simultaneous lift estimate is nonzero, by the
actual prime tiers and frequencies of its original occurrence. -/
theorem movingPrimeOccurrenceLine_nonzero {σ : Type*} {n : ℕ}
    (tier : σ → ℕ) (value : σ → ℕ) (hprime : ∀ i, (value i).Prime)
    (hdisjoint : ∀ i j, tier i ≠ tier j → value i ≠ value j)
    (T : Bool → MovingSlotData σ n) (hlevels : ∀ side, (T side).Levels tier)
    (p : ℕ) (hf : ∀ side, (T side).Frequencies (fun s => (s : ZMod p) ≠ 0))
    (j : MovingPrimeOccurrences value T p) :
    let φ := MovingSlotReversal.naturalReduction p value
    let L := movingPrimeOccurrenceLine value T p j
    φ L.a ≠ 0 ∨ φ L.b ≠ 0 := by
  obtain ⟨i, hi, hpi⟩ := j.2.property
  subst p
  let : Fact (value i).Prime := ⟨hprime i⟩
  let o := movingPrimeOccurrence value T (value i) j
  have hu := (T j.1).occurrence_units_of_prime_types tier value hprime hdisjoint (hlevels j.1)
    o (List.get_mem _ _) i
    ((T j.1).occurrence_compensation_level tier (hlevels j.1) o (List.get_mem _ _) i hi) (hf j.1)
  change MovingSlotReversal.naturalReduction (value i) value (movingSlotLine o.path o.current).a ≠ 0 ∨
    MovingSlotReversal.naturalReduction (value i) value (movingSlotLine o.path o.current).b ≠ 0
  apply movingHistoryLine_nonzero (o.path.map MovingSlotReversal.polynomial)
    o.current.polynomial.v o.current.polynomial.w (MovingSlotReversal.naturalReduction (value i) value)
  · intro s hs
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hs
    exact hu.1 t ht
  · exact hu.2.1
  · exact hu.2.2

/-- Ancestor denominators are also units at the current internal prime. -/
theorem movingPrimeOccurrenceLine_denominator_ne_zero {σ : Type*} {n : ℕ}
    (tier : σ → ℕ) (value : σ → ℕ) (hprime : ∀ i, (value i).Prime)
    (hdisjoint : ∀ i j, tier i ≠ tier j → value i ≠ value j)
    (T : Bool → MovingSlotData σ n) (hlevels : ∀ side, (T side).Levels tier)
    (p : ℕ) (hf : ∀ side, (T side).Frequencies (fun s => (s : ZMod p) ≠ 0))
    (j : MovingPrimeOccurrences value T p) :
    MovingSlotReversal.naturalReduction p value
      (movingPrimeOccurrenceLine value T p j).denominator ≠ 0 := by
  obtain ⟨i, hi, hpi⟩ := j.2.property
  subst p
  let : Fact (value i).Prime := ⟨hprime i⟩
  let o := movingPrimeOccurrence value T (value i) j
  have hu := (T j.1).occurrence_units_of_prime_types tier value hprime hdisjoint (hlevels j.1)
    o (List.get_mem _ _) i
    ((T j.1).occurrence_compensation_level tier (hlevels j.1) o (List.get_mem _ _) i hi) (hf j.1)
  apply movingPolynomialAncestors_denominator (o.path.map MovingSlotReversal.polynomial)
    (MovingSlotReversal.naturalReduction (value i) value)
  intro s hs
  obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hs
  exact (hu.1 t ht).2.2

end Ostmann

end OAI
