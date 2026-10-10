import OAI.NumberTheory.Ostmann.Arithmetic.MovingSampledIndexedProbability

namespace OAI

/-! # Fixed polynomial coordinates for the two-unit line probabilities -/

namespace Ostmann
open scoped Classical BigOperators

theorem movingInternalPrimeProbability_representative {σ : Type*} {n : ℕ}
    (value : σ → ℕ) (T : Bool → MovingSlotData σ n) (rep : σ)
    [Fact (value rep).Prime] (hunique : ∀ i, value i = value rep → i = rep) :
    internalLineProbability false
      (fun j => MovingSlotReversal.naturalReduction (value rep) value
        (movingPrimeOccurrenceLine value T (value rep) j).a)
      (fun j => MovingSlotReversal.naturalReduction (value rep) value
        (movingPrimeOccurrenceLine value T (value rep) j).b) =
    internalLineProbability false
      (fun j => MovingSlotReversal.naturalReduction (value rep) value
        (movingRepresentativeLine T rep j).a)
      (fun j => MovingSlotReversal.naturalReduction (value rep) value
        (movingRepresentativeLine T rep j).b) := by
  unfold internalLineProbability
  simp only [Bool.false_eq_true, ite_false, ← Nat.card_eq_fintype_card]
  apply congrArg (fun k : ℕ => (k : ℝ) / Nat.card ((ZMod (value rep))ˣ × (ZMod (value rep))ˣ))
  exact Nat.card_congr (Equiv.subtypeEquivRight
    (fun z : (ZMod (value rep))ˣ × (ZMod (value rep))ˣ =>
      movingPrimeLineSystem_representative_iff value T rep hunique z.1 z.2))

theorem movingInternalPrimeProbability_indexed {σ : Type*} {n : ℕ}
    (value : σ → ℕ) (T : Bool → MovingSlotData σ n) (rep : σ)
    [Fact (value rep).Prime] (hunique : ∀ i, value i = value rep → i = rep)
    (base : MovingPairRepresentativeOccurrences T rep) :
    internalLineProbability false
      (fun j => MovingSlotReversal.naturalReduction (value rep) value
        (movingPrimeOccurrenceLine value T (value rep) j).a)
      (fun j => MovingSlotReversal.naturalReduction (value rep) value
        (movingPrimeOccurrenceLine value T (value rep) j).b) =
    internalLineProbability false
      (fun j => MovingSlotReversal.naturalReduction (value rep) value
        (movingIndexedLine T rep base j).a)
      (fun j => MovingSlotReversal.naturalReduction (value rep) value
        (movingIndexedLine T rep base j).b) := by
  rw [movingInternalPrimeProbability_representative value T rep hunique]
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
  simp only [Bool.false_eq_true, ite_false, ← Nat.card_eq_fintype_card]
  apply congrArg (fun k : ℕ => (k : ℝ) / Nat.card ((ZMod (value rep))ˣ × (ZMod (value rep))ˣ))
  exact Nat.card_congr (Equiv.subtypeEquivRight
    (fun z : (ZMod (value rep))ˣ × (ZMod (value rep))ˣ => he z.1 z.2))

theorem unitLineProbability_normalized {σ J : Type*} {p : ℕ} [Fact p.Prime]
    (L : J → PolynomialGiantLine σ) (φ : MvPolynomial σ ℤ →+* ZMod p)
    (hd : ∀ j, φ (L j).denominator ≠ 0) :
    internalLineProbability false (fun j => φ (L j).a) (fun j => φ (L j).b) =
      internalLineProbability false (fun j => ((L j).normalized φ).1)
        (fun j => ((L j).normalized φ).2) := by
  have he (x y : ZMod p) : (∀ j, φ (L j).a * x + φ (L j).b * y = 0) ↔
      (∀ j, ((L j).normalized φ).1 * x + ((L j).normalized φ).2 * y = 0) := by
    apply forall_congr'
    intro j
    simp only [PolynomialGiantLine.normalized]
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, div_eq_zero_iff, or_iff_left (hd j)]
  unfold internalLineProbability
  simp only [Bool.false_eq_true, ite_false, ← Nat.card_eq_fintype_card]
  apply congrArg (fun k : ℕ => (k : ℝ) / Nat.card ((ZMod p)ˣ × (ZMod p)ˣ))
  exact Nat.card_congr (Equiv.subtypeEquivRight (fun z : (ZMod p)ˣ × (ZMod p)ˣ => he z.1 z.2))

theorem movingInternalPrimeProbability_indexed_normalized {σ : Type*} {n : ℕ}
    (T : Bool → MovingSlotData σ n) (tier : σ → ℕ) (value : σ → ℕ)
    (hprime : ∀ i, (value i).Prime)
    (hdisjoint : ∀ i j, tier i ≠ tier j → value i ≠ value j)
    (hlevels : ∀ side, (T side).Levels tier)
    (rep : σ) [Fact (value rep).Prime] (base : MovingPairRepresentativeOccurrences T rep)
    (hunique : ∀ i, value i = value rep → i = rep)
    (hf : ∀ side, (T side).Frequencies (fun s => (s : ZMod (value rep)) ≠ 0)) :
    internalLineProbability false
      (fun j => MovingSlotReversal.naturalReduction (value rep) value
        (movingPrimeOccurrenceLine value T (value rep) j).a)
      (fun j => MovingSlotReversal.naturalReduction (value rep) value
        (movingPrimeOccurrenceLine value T (value rep) j).b) =
      internalLineProbability false
        (fun j => ((movingIndexedLine T rep base j).normalized
          (MovingSlotReversal.naturalReduction (value rep) value)).1)
        (fun j => ((movingIndexedLine T rep base j).normalized
          (MovingSlotReversal.naturalReduction (value rep) value)).2) := by
  rw [movingInternalPrimeProbability_indexed value T rep hunique base]
  exact unitLineProbability_normalized (movingIndexedLine T rep base)
    (MovingSlotReversal.naturalReduction (value rep) value)
    (movingIndexedLine_denominator_ne_zero T tier value hprime hdisjoint hlevels rep base hf)

noncomputable def movingSampledInternalPrimeProbability {A : Type*} {N n : ℕ}
    (prime : A → ℕ) (hprime : ∀ a, (prime a).Prime)
    (T : Bool → MovingSlotData (Fin N) n) (x : Fin N → A) (rep : Fin N) : ℝ :=
  letI : Fact (prime (x rep)).Prime := ⟨hprime (x rep)⟩
  internalLineProbability false
    (fun j => MovingSlotReversal.naturalReduction (prime (x rep)) (fun i => prime (x i))
      (movingPrimeOccurrenceLine (fun i => prime (x i)) T (prime (x rep)) j).a)
    (fun j => MovingSlotReversal.naturalReduction (prime (x rep)) (fun i => prime (x i))
      (movingPrimeOccurrenceLine (fun i => prime (x i)) T (prime (x rep)) j).b)

theorem movingSampledIndexedPrimeProbability {A : Type*} {N n : ℕ}
    (prime : A → ℕ) (hprime : ∀ a, (prime a).Prime) (x : Fin N → A)
    (T : Bool → MovingSlotData (Fin N) n) (tier : Fin N → ℕ)
    (hdisjoint : ∀ i j, tier i ≠ tier j → prime (x i) ≠ prime (x j))
    (hlevels : ∀ side, (T side).Levels tier)
    (rep : Fin N) (base : MovingPairRepresentativeOccurrences T rep)
    (hunique : ∀ i, prime (x i) = prime (x rep) → i = rep)
    (hf : ∀ side, (T side).Frequencies (fun s => (s : ZMod (prime (x rep))) ≠ 0)) :
    letI : Fact (prime (x rep)).Prime := ⟨hprime (x rep)⟩
    internalLineProbability false
      (fun j => MovingSlotReversal.naturalReduction (prime (x rep)) (fun i => prime (x i))
        (movingPrimeOccurrenceLine (fun i => prime (x i)) T (prime (x rep)) j).a)
      (fun j => MovingSlotReversal.naturalReduction (prime (x rep)) (fun i => prime (x i))
        (movingPrimeOccurrenceLine (fun i => prime (x i)) T (prime (x rep)) j).b) =
      movingSlotLineProbability (fun a => (prime a : ℤ)) prime hprime
        (fun o => (movingIndexedOccurrence T rep base o).path)
        (fun o => (movingIndexedOccurrence T rep base o).current) false x (x rep) := by
  let : Fact (prime (x rep)).Prime := ⟨hprime (x rep)⟩
  have h := movingInternalPrimeProbability_indexed_normalized T tier (fun i => prime (x i))
    (fun i => hprime (x i)) hdisjoint hlevels rep base hunique hf
  simpa only [movingSlotLineProbability, integerLineReduction,
    MovingSlotReversal.naturalReduction, Int.cast_natCast, movingIndexedLine] using h

end Ostmann

end OAI
