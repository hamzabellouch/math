import OAI.NumberTheory.Ostmann.Arithmetic.MovingFullModulus
import OAI.NumberTheory.Ostmann.Arithmetic.MovingSpectatorScale

namespace OAI

/-! # The complete two-history modulus fits the published progression range -/

namespace Ostmann
open Filter Asymptotics
open scoped BigOperators Classical

def movingFullModulusExponent (n : ℕ) : ℕ :=
  4 * (4 ^ n - 1) + 2 * (2 ^ n - 1) + movingGiantUnitExponent n

theorem movingFullPairModulus_bound {σ I : Type*} (value : σ → ℕ)
    (hvalue : ∀ i, value i ≠ 0) (outside : List ℕ) (childBound pivotBound : ℕ → ℕ)
    {n : ℕ} (T : Bool → MovingSlotData σ n) (hf : ∀ b, (T b).Frequencies (· ≠ 0))
    (q : I → ℕ) (S : Finset I) (B : ℕ) (hB : 1 ≤ B)
    (hfreq : ∀ b, (T b).Frequencies (fun s => s.natAbs ≤ B))
    (hcomp : ∀ b, (T b).CompensationBound value B)
    (hregular : ∀ b, (T b).RegularBound value B) (hout : outside.prod ≤ B) :
    movingFullPairModulus value hvalue outside childBound pivotBound T hf q S ≤
      (B ^ movingFullModulusExponent n * ∏ i ∈ S, q i) ^ 4 := by
  have ht (b : Bool) :
      movingSpectatorModulus value hvalue childBound pivotBound (T b) (hf b) q S *
        (movingGiantUnitPeriod value outside (T b)).natAbs ≤
      B ^ movingFullModulusExponent n * ∏ i ∈ S, q i := by
    calc
      _ ≤ (B ^ (4 * (4 ^ n - 1) + 2 * (2 ^ n - 1)) * ∏ i ∈ S, q i) *
          B ^ movingGiantUnitExponent n :=
        Nat.mul_le_mul (movingSpectatorModulus_bound value hvalue childBound pivotBound
          (T b) (hf b) q S B hB (hfreq b) (hcomp b))
          (movingGiantUnitPeriod_bound value outside (T b) B (hfreq b) (hcomp b) (hregular b) hout)
      _ = _ := by rw [movingFullModulusExponent, pow_add]; ring
  have hp := Finset.prod_le_prod (fun b (_ : b ∈ (Finset.univ : Finset Bool)) => ht b)
  have hh := Nat.pow_le_pow_left hp 2
  simpa only [movingFullPairModulus, movingFullPairModulusBase, Finset.prod_const,
    Finset.card_univ, Fintype.card_bool, ← pow_mul] using hh

theorem movingFullPairModulus_exp {σ I : Type*} (value : σ → ℕ)
    (hvalue : ∀ i, value i ≠ 0) (outside : List ℕ) (childBound pivotBound : ℕ → ℕ)
    {n : ℕ} (T : Bool → MovingSlotData σ n) (hf : ∀ b, (T b).Frequencies (· ≠ 0))
    (q : I → ℕ) (S : Finset I) (B : ℕ) (hB : 1 ≤ B)
    (hfreq : ∀ b, (T b).Frequencies (fun s => s.natAbs ≤ B))
    (hcomp : ∀ b, (T b).CompensationBound value B)
    (hregular : ∀ b, (T b).RegularBound value B) (hout : outside.prod ≤ B)
    (b r : ℝ) (hb : (B : ℝ) ≤ Real.exp b) (hr : ((∏ i ∈ S, q i : ℕ) : ℝ) ≤ Real.exp r) :
    (movingFullPairModulus value hvalue outside childBound pivotBound T hf q S : ℝ) ≤
      Real.exp (4 * ((movingFullModulusExponent n : ℝ) * b + r)) := by
  calc
    _ ≤ ((B : ℝ) ^ movingFullModulusExponent n * (∏ i ∈ S, q i : ℕ)) ^ 4 := by
      exact_mod_cast movingFullPairModulus_bound value hvalue outside childBound pivotBound T hf q S B hB hfreq hcomp hregular hout
    _ ≤ ((Real.exp b) ^ movingFullModulusExponent n * Real.exp r) ^ 4 := by gcongr
    _ = _ := by rw [← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_nat_mul]; congr 1

theorem movingFullModulus_exponent_budget (n : ℕ) (C : ℝ) (d : ℕ) :
    ∀ᶠ L : ℝ in atTop,
      4 * ((movingFullModulusExponent n : ℝ) *
          (C * L ^ d + C * L ^ d * Real.exp ((1 / 100 : ℝ) * L)) +
        ((1 / 1000 : ℝ) * L) * Real.exp ((1 / 1000 : ℝ) * L)) ≤
          Real.exp ((12 / 1000 : ℝ) * L) := by
  let E : ℝ := movingFullModulusExponent n
  have hpoly := (isLittleO_pow_exp_pos_mul_atTop d
    (by norm_num : (0 : ℝ) < 12 / 1000)).const_mul_left (4 * E * C)
  have hprime : (fun L : ℝ => (4 * E * C) * (Real.exp ((1 / 100 : ℝ) * L) * L ^ d)) =o[atTop]
      (fun L => Real.exp ((12 / 1000 : ℝ) * L)) := by
    simpa only [Real.rpow_natCast] using
      (isLittleO_exp_mul_rpow_of_lt (d : ℝ) (by norm_num : (1 / 100 : ℝ) < 12 / 1000)).const_mul_left (4 * E * C)
  have hspec : (fun L : ℝ => (4 / 1000 : ℝ) * (Real.exp ((1 / 1000 : ℝ) * L) * L)) =o[atTop]
      (fun L => Real.exp ((12 / 1000 : ℝ) * L)) := by
    simpa only [Real.rpow_one] using
      (isLittleO_exp_mul_rpow_of_lt 1 (by norm_num : (1 / 1000 : ℝ) < 12 / 1000)).const_mul_left (4 / 1000)
  filter_upwards [((hpoly.add hprime).add hspec).bound (by norm_num : (0 : ℝ) < 1)] with L hL
  simp only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), one_mul] at hL
  have h := (le_abs_self _).trans hL
  change 4 * (E * (C * L ^ d + C * L ^ d * Real.exp ((1 / 100 : ℝ) * L)) +
    ((1 / 1000 : ℝ) * L) * Real.exp ((1 / 1000 : ℝ) * L)) ≤ _
  convert h using 1
  ring

theorem movingFullPairModulus_progression_range {σ : Type*} (n : ℕ) (C : ℝ) (d : ℕ) :
    ∀ᶠ L : ℝ in atTop, ∀ (value : σ → ℕ) (hvalue : ∀ i, value i ≠ 0)
      (outside : List ℕ) (childBound pivotBound : ℕ → ℕ)
      (T : Bool → MovingSlotData σ n) (hf : ∀ b, (T b).Frequencies (· ≠ 0))
      (B : ℕ), 1 ≤ B → (∀ b, (T b).Frequencies (fun s => s.natAbs ≤ B)) →
      (∀ b, (T b).CompensationBound value B) → (∀ b, (T b).RegularBound value B) →
      outside.prod ≤ B →
      (B : ℝ) ≤ Real.exp (C * L ^ d + C * L ^ d * Real.exp ((1 / 100 : ℝ) * L)) →
      ∀ (S : Finset ℕ) (R : ℕ), (∀ q ∈ S, 0 < q ∧ q ≤ R) →
      (R : ℝ) ≤ Real.exp ((1 / 1000 : ℝ) * L) →
      movingFullPairModulus value hvalue outside childBound pivotBound T hf id S ≤
        ⌊Real.exp (Real.exp ((12 / 1000 : ℝ) * L))⌋₊ := by
  filter_upwards [movingFullModulus_exponent_budget n C d, eventually_ge_atTop (0 : ℝ)] with L hL hL0
  intro value hvalue outside childBound pivotBound T hf B hB hfreq hcomp hregular hout hb S R hS hR
  apply Nat.le_floor
  exact (movingFullPairModulus_exp value hvalue outside childBound pivotBound T hf id S B hB
    hfreq hcomp hregular hout _ _ hb (small_spectator_product_exp S R hS _ (by positivity) hR)).trans
      (Real.exp_le_exp.mpr hL)

end Ostmann

end OAI
