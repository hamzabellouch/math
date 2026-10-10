import OAI.NumberTheory.Ostmann.Arithmetic.MovingPrimeHaarError
import OAI.NumberTheory.Ostmann.Arithmetic.MovingPrimeBaseAverage

namespace OAI

/-! # The square error retains the one-over-prime line factor -/

namespace Ostmann
open scoped Classical BigOperators

/-- The base coefficient is a nonnegative indicator, so its absolute average
is exactly its simultaneous line probability. -/
theorem movingInternalBaseFactor_prime_norm_average {σ : Type*} {n : ℕ}
    (value : σ → ℕ) (T : Bool → MovingSlotData σ n) (p : ℕ) [Fact p.Prime] :
    (Fintype.card ((ZMod p)ˣ × (ZMod p)ˣ) : ℝ)⁻¹ *
      (∑ z : (ZMod p)ˣ × (ZMod p)ˣ, ‖movingInternalBaseFactor value T p z.1 z.2‖) =
    internalLineProbability false
      (fun j => MovingSlotReversal.naturalReduction p value
        (movingPrimeOccurrenceLine value T p j).a)
      (fun j => MovingSlotReversal.naturalReduction p value
        (movingPrimeOccurrenceLine value T p j).b) := by
  have he (z : (ZMod p)ˣ × (ZMod p)ˣ) :
      (movingInternalBaseFactor value T p z.1 z.2).re =
        ‖movingInternalBaseFactor value T p z.1 z.2‖ := by
    unfold movingInternalBaseFactor
    split_ifs <;> simp
  have h := congrArg Complex.re (movingInternalBaseFactor_prime_average value T p)
  simpa only [← Complex.ofReal_natCast, ← Complex.ofReal_inv, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, Complex.re_sum, he] using h

theorem movingInternalPrimeAverage_probability_error {σ : Type*} {n : ℕ}
    (tier : σ → ℕ) (value : σ → ℕ) (hprime : ∀ i, (value i).Prime)
    (hdisjoint : ∀ i j, tier i ≠ tier j → value i ≠ value j)
    (T : Bool → MovingSlotData σ n) (hlevels : ∀ side, (T side).Levels tier)
    (p : ℕ) [Fact p.Prime]
    (hf : ∀ side, (T side).Frequencies (fun s => (s : ZMod p) ≠ 0)) :
    let prob := internalLineProbability false
      (fun j => MovingSlotReversal.naturalReduction p value
        (movingPrimeOccurrenceLine value T p j).a)
      (fun j => MovingSlotReversal.naturalReduction p value
        (movingPrimeOccurrenceLine value T p j).b)
    ‖(Fintype.card ((ZMod (p ^ 2))ˣ × (ZMod (p ^ 2))ˣ) : ℂ)⁻¹ *
        (∑ z : (ZMod (p ^ 2))ˣ × (ZMod (p ^ 2))ˣ, movingInternalPairFactor value T p z.1 z.2) -
        (prob : ℂ)‖ ≤ (2 * (2 ^ n - 1 : ℕ) / (p : ℝ)) * prob := by
  have h := movingInternalPrimeAverage_base_error tier value hprime hdisjoint T hlevels p hf
  rw [movingInternalBaseFactor_prime_average, movingInternalBaseFactor_prime_norm_average] at h
  exact h

theorem movingInternalPrimeAverage_probability_norm_le {σ : Type*} {n : ℕ}
    (value : σ → ℕ) (T : Bool → MovingSlotData σ n) (p : ℕ) [Fact p.Prime] :
    ‖(Fintype.card ((ZMod (p ^ 2))ˣ × (ZMod (p ^ 2))ˣ) : ℂ)⁻¹ *
        (∑ z : (ZMod (p ^ 2))ˣ × (ZMod (p ^ 2))ˣ, movingInternalPairFactor value T p z.1 z.2)‖ ≤
      internalLineProbability false
        (fun j => MovingSlotReversal.naturalReduction p value
          (movingPrimeOccurrenceLine value T p j).a)
        (fun j => MovingSlotReversal.naturalReduction p value
          (movingPrimeOccurrenceLine value T p j).b) := by
  have h := movingInternalPrimeAverage_base_norm_le value T p
  rwa [movingInternalBaseFactor_prime_norm_average] at h

end Ostmann

end OAI
