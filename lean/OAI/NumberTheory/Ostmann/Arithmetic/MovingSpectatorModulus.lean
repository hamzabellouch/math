import OAI.NumberTheory.Ostmann.Arithmetic.MovingSpectatorCells
import OAI.NumberTheory.Ostmann.Arithmetic.MovingPeriodScale

namespace OAI

/-! # A concrete modulus for arithmetic support and all spectator trees -/

namespace Ostmann
open scoped Classical BigOperators

noncomputable def movingSpectatorModulus {σ I : Type*} (value : σ → ℕ)
    (hvalue : ∀ i, value i ≠ 0) (childBound pivotBound : ℕ → ℕ) {n : ℕ}
    (T : MovingSlotData σ n) (hf : T.Frequencies (· ≠ 0)) (q : I → ℕ) (S : Finset I) : ℕ :=
  movingTopPeriod value hvalue childBound pivotBound T hf *
    (movingSpectatorDenominator value T).natAbs * ∏ i ∈ S, q i

theorem movingSpectatorModulus_pos {σ I : Type*} (value : σ → ℕ)
    (hvalue : ∀ i, value i ≠ 0) (childBound pivotBound : ℕ → ℕ) {n : ℕ}
    (T : MovingSlotData σ n) (hf : T.Frequencies (· ≠ 0)) (q : I → ℕ) (S : Finset I)
    (hq : ∀ i ∈ S, 0 < q i) :
    0 < movingSpectatorModulus value hvalue childBound pivotBound T hf q S := by
  exact Nat.mul_pos (Nat.mul_pos (movingTopPeriod_pos value hvalue childBound pivotBound T hf)
    (Int.natAbs_pos.mpr (movingSpectatorDenominator_ne_zero value hvalue T hf)))
    (Finset.prod_pos hq)

theorem movingTopPeriod_dvd_spectatorModulus {σ I : Type*} (value : σ → ℕ)
    (hvalue : ∀ i, value i ≠ 0) (childBound pivotBound : ℕ → ℕ) {n : ℕ}
    (T : MovingSlotData σ n) (hf : T.Frequencies (· ≠ 0)) (q : I → ℕ) (S : Finset I) :
    movingTopPeriod value hvalue childBound pivotBound T hf ∣
      movingSpectatorModulus value hvalue childBound pivotBound T hf q S := by
  exact ⟨(movingSpectatorDenominator value T).natAbs * ∏ i ∈ S, q i, by
    simp only [movingSpectatorModulus, mul_assoc]⟩

theorem spectator_dvd_movingSpectatorModulus {σ I : Type*} (value : σ → ℕ)
    (hvalue : ∀ i, value i ≠ 0) (childBound pivotBound : ℕ → ℕ) {n : ℕ}
    (T : MovingSlotData σ n) (hf : T.Frequencies (· ≠ 0)) (q : I → ℕ) (S : Finset I)
    (i : I) (hi : i ∈ S) :
    (q i : ℤ) * movingSpectatorDenominator value T ∣
      (movingSpectatorModulus value hvalue childBound pivotBound T hf q S : ℤ) := by
  obtain ⟨z, hz⟩ := Int.dvd_natAbs.mpr (dvd_refl (movingSpectatorDenominator value T))
  obtain ⟨w, hw⟩ := Finset.dvd_prod_of_mem q hi
  refine ⟨(movingTopPeriod value hvalue childBound pivotBound T hf : ℤ) * z * w, ?_⟩
  simp only [movingSpectatorModulus, Nat.cast_mul, hz, hw]
  ring

theorem movingSpectatorModulus_bound {σ I : Type*} (value : σ → ℕ)
    (hvalue : ∀ i, value i ≠ 0) (childBound pivotBound : ℕ → ℕ) {n : ℕ}
    (T : MovingSlotData σ n) (hf : T.Frequencies (· ≠ 0)) (q : I → ℕ) (S : Finset I)
    (B : ℕ) (hB : 1 ≤ B) (hfreq : T.Frequencies (fun s => s.natAbs ≤ B))
    (hcomp : T.CompensationBound value B) :
    movingSpectatorModulus value hvalue childBound pivotBound T hf q S ≤
      B ^ (4 * (4 ^ n - 1) + 2 * (2 ^ n - 1)) * ∏ i ∈ S, q i := by
  unfold movingSpectatorModulus
  apply Nat.mul_le_mul_right
  calc
    _ ≤ B ^ (4 * (4 ^ n - 1)) * B ^ (2 * (2 ^ n - 1)) :=
      Nat.mul_le_mul (movingTopPeriod_bound value hvalue childBound pivotBound T hf B hB hfreq hcomp)
        (movingSpectatorDenominator_bound value T B hfreq hcomp)
    _ = _ := (pow_add _ _ _).symm

/-- This bound applies to a fixed finite set of distinct spectator primes
using only their upper endpoint. No prime number theorem is required. -/
theorem small_spectator_product_bound (S : Finset ℕ) (R : ℕ)
    (hS : ∀ q ∈ S, 0 < q ∧ q ≤ R) : ∏ q ∈ S, q ≤ R ^ R := by
  have hsub : S ⊆ Finset.Icc 1 R := by
    intro q hq
    exact Finset.mem_Icc.mpr ⟨(hS q hq).1, (hS q hq).2⟩
  have hcard : S.card ≤ R := (Finset.card_le_card hsub).trans (by simp)
  calc
    _ ≤ ∏ _q ∈ S, R := Finset.prod_le_prod (fun q hq => (hS q hq).2)
    _ = R ^ S.card := by simp
    _ ≤ R ^ R := by
      by_cases hR : R = 0
      · subst R
        have : S = ∅ := Finset.card_eq_zero.mp (by omega)
        subst S
        simp
      · exact Nat.pow_le_pow_right (by omega) hcard

theorem small_spectator_product_exp (S : Finset ℕ) (R : ℕ)
    (hS : ∀ q ∈ S, 0 < q ∧ q ≤ R) (x : ℝ) (hx : 0 ≤ x)
    (hR : (R : ℝ) ≤ Real.exp x) :
    (∏ q ∈ S, q : ℕ) ≤ Real.exp (x * Real.exp x) := by
  calc
    ((∏ q ∈ S, q : ℕ) : ℝ) ≤ (R : ℝ) ^ R := by
      exact_mod_cast small_spectator_product_bound S R hS
    _ ≤ (Real.exp x) ^ R := by gcongr
    _ = Real.exp ((R : ℝ) * x) := (Real.exp_nat_mul x R).symm
    _ ≤ Real.exp (x * Real.exp x) := by
      apply Real.exp_le_exp.mpr
      nlinarith

theorem movingSpectatorModulus_exp {σ : Type*} (value : σ → ℕ)
    (hvalue : ∀ i, value i ≠ 0) (childBound pivotBound : ℕ → ℕ) {n : ℕ}
    (T : MovingSlotData σ n) (hf : T.Frequencies (· ≠ 0)) (S : Finset ℕ)
    (B : ℕ) (hB : 1 ≤ B) (hfreq : T.Frequencies (fun s => s.natAbs ≤ B))
    (hcomp : T.CompensationBound value B) (b r : ℝ)
    (hb : (B : ℝ) ≤ Real.exp b) (hr : ((∏ q ∈ S, q : ℕ) : ℝ) ≤ Real.exp r) :
    (movingSpectatorModulus value hvalue childBound pivotBound T hf id S : ℝ) ≤
      Real.exp (((4 * (4 ^ n - 1) + 2 * (2 ^ n - 1) : ℕ) : ℝ) * b + r) := by
  calc
    _ ≤ (B : ℝ) ^ (4 * (4 ^ n - 1) + 2 * (2 ^ n - 1)) * (∏ q ∈ S, q : ℕ) := by
      exact_mod_cast movingSpectatorModulus_bound value hvalue childBound pivotBound T hf id S B hB hfreq hcomp
    _ ≤ (Real.exp b) ^ (4 * (4 ^ n - 1) + 2 * (2 ^ n - 1)) * Real.exp r := by gcongr
    _ = _ := by rw [← Real.exp_nat_mul, ← Real.exp_add]

end Ostmann

end OAI
