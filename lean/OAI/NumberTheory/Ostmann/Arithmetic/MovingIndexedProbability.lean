import OAI.NumberTheory.Ostmann.Arithmetic.MovingIndexedLineSystem

namespace OAI

/-! # Normalizing the fixed occurrence system for the small-prime comparison -/

namespace Ostmann
open scoped Classical

theorem externalLineProbability_normalized {σ J : Type*} {p : ℕ} [Fact p.Prime]
    (L : J → PolynomialGiantLine σ) (φ : MvPolynomial σ ℤ →+* ZMod p)
    (hd : ∀ j, φ (L j).denominator ≠ 0) :
    internalLineProbability true (fun j => φ (L j).a) (fun j => φ (L j).b) =
      internalLineProbability true (fun j => ((L j).normalized φ).1)
        (fun j => ((L j).normalized φ).2) := by
  have he (x y : ZMod p) : (∀ j, φ (L j).a * x + φ (L j).b * y = 0) ↔
      (∀ j, ((L j).normalized φ).1 * x + ((L j).normalized φ).2 * y = 0) := by
    apply forall_congr'
    intro j
    simp only [PolynomialGiantLine.normalized]
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, div_eq_zero_iff, or_iff_left (hd j)]
  unfold internalLineProbability
  simp only [ite_true, ← Nat.card_eq_fintype_card]
  apply congrArg (fun k : ℕ => (k : ℝ) / Nat.card (ZMod p × (ZMod p)ˣ))
  exact Nat.card_congr (Equiv.subtypeEquivRight (fun z : ZMod p × (ZMod p)ˣ => he z.1 z.2))

theorem movingIndexedLine_denominator_ne_zero {σ : Type*} {n : ℕ}
    (T : Bool → MovingSlotData σ n) (tier : σ → ℕ) (value : σ → ℕ)
    (hprime : ∀ i, (value i).Prime)
    (hdisjoint : ∀ i j, tier i ≠ tier j → value i ≠ value j)
    (hlevels : ∀ side, (T side).Levels tier)
    (rep : σ) (base : MovingPairRepresentativeOccurrences T rep)
    (hf : ∀ side, (T side).Frequencies (fun s => (s : ZMod (value rep)) ≠ 0))
    (o : MovingPairOccurrenceIndex T) :
    MovingSlotReversal.naturalReduction (value rep) value
      (movingIndexedLine T rep base o).denominator ≠ 0 := by
  let : Fact (value rep).Prime := ⟨hprime rep⟩
  have hu := movingIndexedOccurrence_units T tier value hprime hdisjoint hlevels rep base hf o
  change MovingSlotReversal.naturalReduction (value rep) value
    (movingPolynomialAncestors
      ((movingIndexedOccurrence T rep base o).path.map MovingSlotReversal.polynomial)).denominator ≠ 0
  apply movingPolynomialAncestors_denominator
    ((movingIndexedOccurrence T rep base o).path.map MovingSlotReversal.polynomial)
    (MovingSlotReversal.naturalReduction (value rep) value)
  intro s hs
  obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hs
  exact (hu.1 t ht).2.2

theorem movingInternalBaseProbability_indexed_normalized {σ : Type*} {n : ℕ}
    (T : Bool → MovingSlotData σ n) (tier : σ → ℕ) (value : σ → ℕ)
    (hprime : ∀ i, (value i).Prime)
    (hdisjoint : ∀ i j, tier i ≠ tier j → value i ≠ value j)
    (hlevels : ∀ side, (T side).Levels tier)
    (rep : σ) [Fact (value rep).Prime] (base : MovingPairRepresentativeOccurrences T rep)
    (hunique : ∀ i, value i = value rep → i = rep)
    (hf : ∀ side, (T side).Frequencies (fun s => (s : ZMod (value rep)) ≠ 0)) :
    internalLineProbability true
      (fun j => MovingSlotReversal.naturalReduction (value rep) value
        (movingPrimeOccurrenceLine value T (value rep) j).a)
      (fun j => MovingSlotReversal.naturalReduction (value rep) value
        (movingPrimeOccurrenceLine value T (value rep) j).b) =
      internalLineProbability true
        (fun j => ((movingIndexedLine T rep base j).normalized
          (MovingSlotReversal.naturalReduction (value rep) value)).1)
        (fun j => ((movingIndexedLine T rep base j).normalized
          (MovingSlotReversal.naturalReduction (value rep) value)).2) := by
  rw [movingInternalBaseProbability_indexed value T rep hunique base]
  exact externalLineProbability_normalized (movingIndexedLine T rep base)
    (MovingSlotReversal.naturalReduction (value rep) value)
    (movingIndexedLine_denominator_ne_zero T tier value hprime hdisjoint hlevels rep base hf)

end Ostmann

end OAI
