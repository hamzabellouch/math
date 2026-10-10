import OAI.NumberTheory.Ostmann.Arithmetic.MovingSeparatedPair

namespace OAI

/-! # Actual internal-prime factors before averaging -/

namespace Ostmann
open scoped Classical BigOperators ComplexConjugate

/-- All occurrences of a fixed internal prime impose their line modulo `p`
and exclude its zero lift modulo `p²`. Repeated occurrences remain simultaneous. -/
noncomputable def movingInternalLocalSupport {σ : Type*} (value : σ → ℕ)
    {n : ℕ} (T : MovingSlotData σ n) (p : ℕ) (x y : ZMod (p ^ 2)) : Prop :=
  ∀ o ∈ T.occurrences, ∀ i ∈ o.current.compensationSlots, value i = p →
    let φ := MovingSlotReversal.naturalReduction (p ^ 2) value
    let z := φ (movingSlotLine o.path o.current).a * x +
      φ (movingSlotLine o.path o.current).b * y
    squareReduction p z = 0 ∧ z ≠ 0

theorem movingInternalLocalSupport_iff {σ : Type*} (value : σ → ℕ)
    {n : ℕ} (T : MovingSlotData σ n) (P : Finset ℕ)
    (hcover : ∀ o ∈ T.occurrences, ∀ i ∈ o.current.compensationSlots, value i ∈ P)
    (x y : ℤ) :
    (∀ p ∈ P, movingInternalLocalSupport value T p x y) ↔
      movingPrimeLineSupport value T x y ∧ movingSquareLineSupport value T x y := by
  have he (p : ℕ) (o : MovingSlotOccurrence σ) :
      squareReduction p
          (MovingSlotReversal.naturalReduction (p ^ 2) value (movingSlotLine o.path o.current).a *
            (x : ZMod (p ^ 2)) +
           MovingSlotReversal.naturalReduction (p ^ 2) value (movingSlotLine o.path o.current).b *
            (y : ZMod (p ^ 2))) =
        MovingSlotReversal.naturalReduction p value (movingSlotLine o.path o.current).a *
            (x : ZMod p) +
          MovingSlotReversal.naturalReduction p value (movingSlotLine o.path o.current).b *
            (y : ZMod p) := by
    simp
  constructor
  · intro h
    constructor
    · intro o ho i hi
      have hz := (h (value i) (hcover o ho i hi) o ho i hi rfl).1
      dsimp only at hz ⊢
      rw [he] at hz
      exact hz
    · intro o ho i hi
      exact (h (value i) (hcover o ho i hi) o ho i hi rfl).2
  · rintro ⟨hline, hsquare⟩ p _ o ho i hi rfl
    exact ⟨by simpa only [he] using hline o ho i hi, hsquare o ho i hi⟩

noncomputable def movingInternalPairFactor {σ : Type*} (value : σ → ℕ)
    {n : ℕ} (T : Bool → MovingSlotData σ n) (p : ℕ)
    (x y : ZMod (p ^ 2)) : ℂ :=
  if ∀ side, movingInternalLocalSupport value (T side) p x y then 1 else 0

theorem movingInternalPairFactor_product {σ : Type*} (value : σ → ℕ)
    {n : ℕ} (T : Bool → MovingSlotData σ n) (P : Finset ℕ)
    (hcover : ∀ side, ∀ o ∈ (T side).occurrences,
      ∀ i ∈ o.current.compensationSlots, value i ∈ P) (x y : ℤ) :
    (∏ p ∈ P, movingInternalPairFactor value T p x y) =
      if ∀ side, movingPrimeLineSupport value (T side) x y ∧
        movingSquareLineSupport value (T side) x y then 1 else 0 := by
  have hiff : (∀ p ∈ P, ∀ side, movingInternalLocalSupport value (T side) p x y) ↔
      ∀ side, movingPrimeLineSupport value (T side) x y ∧
        movingSquareLineSupport value (T side) x y := by
    constructor
    · intro h side
      exact (movingInternalLocalSupport_iff value (T side) P (hcover side) x y).mp
        (fun p hp => h p hp side)
    · intro h p hp side
      exact (movingInternalLocalSupport_iff value (T side) P (hcover side) x y).mpr
        (h side) p hp
  by_cases h : ∀ p ∈ P, ∀ side, movingInternalLocalSupport value (T side) p x y
  · rw [ite_eq_left (hiff.mp h)]
    apply Finset.prod_eq_one
    intro p hp
    exact ite_eq_left (h p hp)
  · rw [ite_eq_right (fun hn => h (hiff.mpr hn))]
    obtain ⟨p, hp, hn⟩ := not_forall₂.mp h
    exact Finset.prod_eq_zero hp (ite_eq_right hn)

end Ostmann

end OAI
