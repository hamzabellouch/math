import OAI.NumberTheory.Ostmann.Arithmetic.MovingInternalFiber
import OAI.NumberTheory.Ostmann.Construction.ExternalSquareCoordinates

namespace OAI

/-! # The relative square error in the original local Haar average -/

namespace Ostmann
open scoped Classical BigOperators

theorem movingInternalPairFactor_fiber_norm_le {σ : Type*} {n : ℕ}
    (value : σ → ℕ) (T : Bool → MovingSlotData σ n) (p : ℕ) [Fact p.Prime]
    (x₀ y₀ : ZMod p) (v : SquareLiftPairs p x₀ y₀) :
    ‖movingInternalPairFactor value T p v.1.val v.2.val‖ ≤
      ‖movingInternalBaseFactor value T p x₀ y₀‖ := by
  rw [movingInternalPairFactor_fiber, norm_mul]
  apply mul_le_of_le_one_right (norm_nonneg _)
  split_ifs <;> norm_num

theorem movingInternalPairFactor_normalized_fiber_norm_le {σ : Type*} {n : ℕ}
    (value : σ → ℕ) (T : Bool → MovingSlotData σ n) (p : ℕ) [Fact p.Prime]
    (x₀ y₀ : ZMod p) :
    ‖((p : ℂ) ^ 2)⁻¹ *
        (∑ v : SquareLiftPairs p x₀ y₀, movingInternalPairFactor value T p v.1.val v.2.val)‖ ≤
      ‖movingInternalBaseFactor value T p x₀ y₀‖ := by
  have hp : (p : ℝ) ^ 2 ≠ 0 := pow_ne_zero _ (by exact_mod_cast (Fact.out : p.Prime).ne_zero)
  rw [norm_mul, norm_inv, norm_pow, Complex.norm_natCast]
  calc
    _ ≤ ((p : ℝ) ^ 2)⁻¹ * ∑ _v : SquareLiftPairs p x₀ y₀,
        ‖movingInternalBaseFactor value T p x₀ y₀‖ := by
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (sq_nonneg _))
      exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun v _ =>
        movingInternalPairFactor_fiber_norm_le value T p x₀ y₀ v)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
        squareLiftPairs_card, Nat.cast_pow]
      rw [← mul_assoc, inv_mul_cancel₀ hp, one_mul]

theorem movingInternalPairFactor_normalized_fiber_error {σ : Type*} {n : ℕ}
    (tier : σ → ℕ) (value : σ → ℕ) (hprime : ∀ i, (value i).Prime)
    (hdisjoint : ∀ i j, tier i ≠ tier j → value i ≠ value j)
    (T : Bool → MovingSlotData σ n) (hlevels : ∀ side, (T side).Levels tier)
    (p : ℕ) [Fact p.Prime]
    (hf : ∀ side, (T side).Frequencies (fun s => (s : ZMod p) ≠ 0))
    (x₀ y₀ : ZMod p) (hy : y₀ ≠ 0) :
    ‖((p : ℂ) ^ 2)⁻¹ *
        (∑ v : SquareLiftPairs p x₀ y₀, movingInternalPairFactor value T p v.1.1 v.2.1) -
        movingInternalBaseFactor value T p x₀ y₀‖ ≤
      (2 * (2 ^ n - 1 : ℕ) / (p : ℝ)) * ‖movingInternalBaseFactor value T p x₀ y₀‖ := by
  let A := ∀ j : MovingPrimeOccurrences value T p,
    let φ := MovingSlotReversal.naturalReduction p value
    let L := movingPrimeOccurrenceLine value T p j
    φ L.a * x₀ + φ L.b * y₀ = 0
  by_cases h : A
  · have hval : movingInternalBaseFactor value T p x₀ y₀ = 1 := ite_eq_left h
    have hb := movingInternalPairFactor_fiber_error tier value hprime hdisjoint T hlevels p hf x₀ y₀ hy h
    have hp : (p : ℂ) ^ 2 ≠ 0 := pow_ne_zero _ (by exact_mod_cast (Fact.out : p.Prime).ne_zero)
    have he (z : ℂ) : ((p : ℂ) ^ 2)⁻¹ * z - 1 = ((p : ℂ) ^ 2)⁻¹ * (z - (p : ℂ) ^ 2) := by
      rw [mul_sub, inv_mul_cancel₀ hp]
    rw [hval, norm_one, mul_one, he, norm_mul, norm_inv, norm_pow, Complex.norm_natCast]
    exact hb
  · have hval : movingInternalBaseFactor value T p x₀ y₀ = 0 := ite_eq_right h
    have hz (v : SquareLiftPairs p x₀ y₀) : movingInternalPairFactor value T p v.1.1 v.2.1 = 0 := by
      rw [movingInternalPairFactor_fiber, hval, zero_mul]
    simp only [hz, Finset.sum_const_zero, mul_zero, hval, sub_self, norm_zero, le_refl]

end Ostmann

end OAI
