import OAI.NumberTheory.Ostmann.Arithmetic.MovingInternalBaseAverage
import OAI.NumberTheory.Ostmann.Arithmetic.ArithmeticLineIntegration

namespace OAI

/-! # Actual internal-prime averages after removing their square exclusions -/

namespace Ostmann
open scoped Classical BigOperators

/-- The field average is the exact simultaneous line probability for all
occurrences of the prime in both original histories. -/
theorem movingInternalBaseFactor_prime_average {σ : Type*} {n : ℕ}
    (value : σ → ℕ) (T : Bool → MovingSlotData σ n) (p : ℕ) [Fact p.Prime] :
    (Fintype.card ((ZMod p)ˣ × (ZMod p)ˣ) : ℂ)⁻¹ *
      (∑ z : (ZMod p)ˣ × (ZMod p)ˣ, movingInternalBaseFactor value T p z.1 z.2) =
    (internalLineProbability false
      (fun j => MovingSlotReversal.naturalReduction p value
        (movingPrimeOccurrenceLine value T p j).a)
      (fun j => MovingSlotReversal.naturalReduction p value
        (movingPrimeOccurrenceLine value T p j).b) : ℂ) := by
  classical
  let P := fun z : (ZMod p)ˣ × (ZMod p)ˣ => ∀ j : MovingPrimeOccurrences value T p,
    let φ := MovingSlotReversal.naturalReduction p value
    let L := movingPrimeOccurrenceLine value T p j
    φ L.a * z.1 + φ L.b * z.2 = 0
  have hs : (∑ z : (ZMod p)ˣ × (ZMod p)ˣ, movingInternalBaseFactor value T p z.1 z.2) =
      (Fintype.card {z : (ZMod p)ˣ × (ZMod p)ˣ // P z} : ℂ) := by
    rw [Fintype.card_subtype]
    simp only [movingInternalBaseFactor, P, ← Finset.sum_filter, Finset.sum_const,
      nsmul_eq_mul, mul_one]
  dsimp only [P] at hs
  rw [hs]
  simp only [internalLineProbability, Bool.false_eq_true, ite_false, Complex.ofReal_div, Complex.ofReal_natCast]
  rw [mul_comm, ← div_eq_mul_inv]
  simp only [← Nat.card_eq_fintype_card]

/-- All rows and all cleared denominators in this line probability come from
the actual moving trees. Thus the polynomial flags used later are exact. -/
theorem movingInternalPrimeProbability_eq_flags {σ : Type*} {n : ℕ}
    (tier : σ → ℕ) (value : σ → ℕ) (hprime : ∀ i, (value i).Prime)
    (hdisjoint : ∀ i j, tier i ≠ tier j → value i ≠ value j)
    (T : Bool → MovingSlotData σ n) (hlevels : ∀ side, (T side).Levels tier)
    (p : ℕ) [Fact p.Prime]
    (hf : ∀ side, (T side).Frequencies (fun s => (s : ZMod p) ≠ 0))
    (base : MovingPrimeOccurrences value T p) :
    internalLineProbability false
      (fun j => MovingSlotReversal.naturalReduction p value
        (movingPrimeOccurrenceLine value T p j).a)
      (fun j => MovingSlotReversal.naturalReduction p value
        (movingPrimeOccurrenceLine value T p j).b) =
      internalLineFlagWeight false p (fun s => arithmeticTestFlag
        (MovingSlotReversal.naturalReduction p value
          (lineTestPolynomials (movingPrimeOccurrenceLine value T p) base s) = 0)) := by
  classical
  let φ := MovingSlotReversal.naturalReduction p value
  let L := movingPrimeOccurrenceLine value T p
  have hd := movingPrimeOccurrenceLine_denominator_ne_zero tier value hprime hdisjoint T hlevels p hf
  have hr := movingPrimeOccurrenceLine_nonzero tier value hprime hdisjoint T hlevels p hf base
  have he (x y : ZMod p) : (∀ j, φ (L j).a * x + φ (L j).b * y = 0) ↔
      (∀ j, ((L j).normalized φ).1 * x + ((L j).normalized φ).2 * y = 0) := by
    apply forall_congr'
    intro j
    simp only [PolynomialGiantLine.normalized]
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, div_eq_zero_iff, or_iff_left (hd j)]
  have hc := Nat.card_congr (Equiv.subtypeEquivRight
    (fun z : (ZMod p)ˣ × (ZMod p)ˣ => he z.1 z.2))
  have hr' : ((L base).normalized φ).1 ≠ 0 ∨ ((L base).normalized φ).2 ≠ 0 := by
    have hz := (L base).normalized_zero_iff φ (hd base)
    exact hr.imp (fun h h0 => h (hz.1.mp h0)) (fun h h0 => h (hz.2.mp h0))
  have hext := unit_lineSystem_integral_eq_flags L base φ hd hr'
  unfold internalLineProbability
  simp only [Bool.false_eq_true, ite_false, ← Nat.card_eq_fintype_card]
  simp only [← Nat.card_eq_fintype_card] at hext
  change (Nat.card {z : (ZMod p)ˣ × (ZMod p)ˣ //
    ∀ j, φ (L j).a * z.1 + φ (L j).b * z.2 = 0} : ℝ) /
      Nat.card ((ZMod p)ˣ × (ZMod p)ˣ) = _
  rw [hc]
  exact hext

end Ostmann

end OAI
