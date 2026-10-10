import OAI.NumberTheory.Ostmann.Arithmetic.MovingInternalProbabilityError
import OAI.NumberTheory.Ostmann.Preliminaries.FiniteRelativeProductError

namespace OAI

/-! # Simultaneous square removal with the full internal-prime scale -/

namespace Ostmann
open scoped Classical BigOperators

noncomputable def movingInternalHaarAverage {σ : Type*} {n : ℕ}
    (value : σ → ℕ) (T : Bool → MovingSlotData σ n) (p : ℕ) [Fact p.Prime] : ℂ :=
  (Fintype.card (ZMod (p ^ 2) × (ZMod (p ^ 2))ˣ) : ℂ)⁻¹ *
    ∑ z : ZMod (p ^ 2) × (ZMod (p ^ 2))ˣ, movingInternalPairFactor value T p z.1 z.2

noncomputable def movingInternalLineProbability {σ : Type*} {n : ℕ}
    (value : σ → ℕ) (T : Bool → MovingSlotData σ n) (p : ℕ) [Fact p.Prime] : ℝ :=
  internalLineProbability true
    (fun j => MovingSlotReversal.naturalReduction p value
      (movingPrimeOccurrenceLine value T p j).a)
    (fun j => MovingSlotReversal.naturalReduction p value
      (movingPrimeOccurrenceLine value T p j).b)

theorem movingInternalLineProbability_nonneg {σ : Type*} {n : ℕ}
    (value : σ → ℕ) (T : Bool → MovingSlotData σ n) (p : ℕ) [Fact p.Prime] :
    0 ≤ movingInternalLineProbability value T p := internalLineProbability_nonneg _ _ _

theorem movingInternalLineProbability_le_inv {σ : Type*} {n : ℕ}
    (tier : σ → ℕ) (value : σ → ℕ) (hprime : ∀ i, (value i).Prime)
    (hdisjoint : ∀ i j, tier i ≠ tier j → value i ≠ value j)
    (T : Bool → MovingSlotData σ n) (hlevels : ∀ side, (T side).Levels tier)
    (p : ℕ) [Fact p.Prime]
    (hf : ∀ side, (T side).Frequencies (fun s => (s : ZMod p) ≠ 0))
    (base : MovingPrimeOccurrences value T p) :
    movingInternalLineProbability value T p ≤ (p : ℝ)⁻¹ := by
  unfold movingInternalLineProbability
  rw [movingInternalBaseProbability_eq_flags tier value hprime hdisjoint T hlevels p hf base]
  unfold internalLineFlagWeight internalLineScalar
  simp only [ite_true]
  split_ifs
  · rfl
  · exact inv_nonneg.mpr (Nat.cast_nonneg _)

/-- The simultaneous replacement is relative to the complete product of line
probabilities, including the factor from every distinct internal prime. -/
theorem movingInternalProduct_error {σ : Type*} {n : ℕ}
    (tier : σ → ℕ) (value : σ → ℕ) (hprime : ∀ i, (value i).Prime)
    (hdisjoint : ∀ i j, tier i ≠ tier j → value i ≠ value j)
    (T : Bool → MovingSlotData σ n) (hlevels : ∀ side, (T side).Levels tier)
    (P : Finset ℕ) [∀ p : P, Fact p.val.Prime]
    (hf : ∀ p : P, ∀ side, (T side).Frequencies (fun s => (s : ZMod p.val) ≠ 0)) :
    ‖(∏ p : P, movingInternalHaarAverage value T p.val) -
        ∏ p : P, (movingInternalLineProbability value T p.val : ℂ)‖ ≤
      (2 * (2 ^ n - 1 : ℕ) * ∑ p : P, (p.val : ℝ)⁻¹) *
        ∏ p : P, movingInternalLineProbability value T p.val := by
  have h := finite_relative_product_error (Finset.univ : Finset P)
    (fun p => movingInternalHaarAverage value T p.val)
    (fun p => (movingInternalLineProbability value T p.val : ℂ))
    (fun p => movingInternalLineProbability value T p.val)
    (fun p => 2 * (2 ^ n - 1 : ℕ) / (p.val : ℝ))
    (fun p _ => movingInternalLineProbability_nonneg value T p.val)
    (fun p _ => div_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg _)) (Nat.cast_nonneg _))
    (fun p _ => movingInternalPairFactor_probability_norm_le value T p.val)
    (fun p _ => by rw [Complex.norm_real, Real.norm_of_nonneg
      (movingInternalLineProbability_nonneg value T p.val)])
    (fun p _ => movingInternalPairFactor_probability_error tier value hprime hdisjoint T hlevels p.val (hf p))
  simpa only [div_eq_mul_inv, ← Finset.mul_sum] using h

/-- The external coefficient may grow with the sampled internal primes. Only
its product with the actual line probabilities needs to be bounded. -/
theorem movingInternalProduct_weighted_error {σ : Type*} {n : ℕ}
    (tier : σ → ℕ) (value : σ → ℕ) (hprime : ∀ i, (value i).Prime)
    (hdisjoint : ∀ i j, tier i ≠ tier j → value i ≠ value j)
    (T : Bool → MovingSlotData σ n) (hlevels : ∀ side, (T side).Levels tier)
    (P : Finset ℕ) [∀ p : P, Fact p.val.Prime]
    (hf : ∀ p : P, ∀ side, (T side).Frequencies (fun s => (s : ZMod p.val) ≠ 0))
    (W : ℂ) (B : ℝ)
    (hW : ‖W‖ * (∏ p : P, movingInternalLineProbability value T p.val) ≤ B) :
    ‖W * ((∏ p : P, movingInternalHaarAverage value T p.val) -
        ∏ p : P, (movingInternalLineProbability value T p.val : ℂ))‖ ≤
      B * (2 * (2 ^ n - 1 : ℕ) * ∑ p : P, (p.val : ℝ)⁻¹) := by
  have hK : 0 ≤ 2 * (2 ^ n - 1 : ℕ) * ∑ p : P, (p.val : ℝ)⁻¹ := by positivity
  rw [norm_mul]
  apply (mul_le_mul_of_nonneg_left
    (movingInternalProduct_error tier value hprime hdisjoint T hlevels P hf) (norm_nonneg W)).trans
  calc
    _ = (‖W‖ * (∏ p : P, movingInternalLineProbability value T p.val)) *
        (2 * (2 ^ n - 1 : ℕ) * ∑ p : P, (p.val : ℝ)⁻¹) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hW hK

end Ostmann

end OAI
