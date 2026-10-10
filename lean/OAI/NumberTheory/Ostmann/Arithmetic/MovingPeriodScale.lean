import OAI.NumberTheory.Ostmann.Arithmetic.MovingSamplePeriod
import OAI.NumberTheory.Ostmann.Arithmetic.ArithmeticErrorRates

namespace OAI

/-! # The constructed moving modulus fits the giant progression range -/

namespace Ostmann
open Filter Asymptotics
open scoped Classical

theorem movingSample_topPeriod_exp {σ : Type*} (value : σ → ℕ)
    (hvalue : ∀ i, value i ≠ 0) (P V : ℕ) (hP : 1 ≤ P) (hV : 1 ≤ V)
    (hvalueP : ∀ i, value i ≤ P) (childBound pivotBound : ℕ → ℕ)
    (n : ℕ) (t : FrequencyTree ℤ n) (small bulk : TreeLeafTuple (List σ) n)
    (samples : MovingSampleSlots σ n)
    (hf : (buildMovingSlotData n t small bulk samples).Frequencies (· ≠ 0))
    (hfreq : (buildMovingSlotData n t small bulk samples).Frequencies (fun s => s.natAbs ≤ V))
    (v p : ℝ) (hv : (V : ℝ) ≤ Real.exp v) (hp : (P : ℝ) ≤ Real.exp p) :
    (movingTopPeriod value hvalue childBound pivotBound
      (buildMovingSlotData n t small bulk samples) hf : ℝ) ≤
        Real.exp ((4 * (4 ^ n - 1) : ℕ) * (v + (4 * 2 ^ n : ℕ) * p)) := by
  have h := movingSample_topPeriod_bound value hvalue P V hP hV hvalueP
    childBound pivotBound n t small bulk samples hf hfreq
  calc
    _ ≤ ((V : ℝ) * (P : ℝ) ^ (4 * 2 ^ n)) ^ (4 * (4 ^ n - 1)) := by exact_mod_cast h
    _ ≤ (Real.exp v * (Real.exp p) ^ (4 * 2 ^ n)) ^ (4 * (4 ^ n - 1)) := by gcongr
    _ = _ := by rw [← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_nat_mul]

/-- Fixed depth and all fixed constants are absorbed by the strict .010/.012
exponent gap in the source. The cutoff is uniform in the sampled primes. -/
theorem movingSample_period_exponent_budget (n : ℕ) (C : ℝ) :
    ∀ᶠ L : ℝ in atTop,
      ((4 * (4 ^ n - 1) : ℕ) : ℝ) *
          (C * L + (4 * 2 ^ n : ℕ) * (C * Real.exp ((1 / 100 : ℝ) * L))) ≤
        Real.exp ((12 / 1000 : ℝ) * L) := by
  let E : ℝ := (4 * (4 ^ n - 1) : ℕ)
  let F : ℝ := (4 * 2 ^ n : ℕ)
  have hlin : (fun L : ℝ => (E * C) * L) =o[atTop]
      (fun L => Real.exp ((12 / 1000 : ℝ) * L)) := by
    simpa only [pow_one] using
      (isLittleO_pow_exp_pos_mul_atTop 1 (by norm_num : (0 : ℝ) < 12 / 1000)).const_mul_left (E * C)
  have hexp : (fun L : ℝ => (E * F * C) * Real.exp ((1 / 100 : ℝ) * L)) =o[atTop]
      (fun L => Real.exp ((12 / 1000 : ℝ) * L)) := by
    simpa only [Real.rpow_zero, mul_one] using
      (isLittleO_exp_mul_rpow_of_lt 0 (by norm_num : (1 / 100 : ℝ) < 12 / 1000)).const_mul_left (E * F * C)
  filter_upwards [(hlin.add hexp).bound (by norm_num : (0 : ℝ) < 1)] with L hL
  simp only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), one_mul] at hL
  have h := (le_abs_self _).trans hL
  change E * (C * L + F * (C * Real.exp ((1 / 100 : ℝ) * L))) ≤ _
  nlinarith only [h]

/-- An actual integer modulus bound for the published giant progression input.
Neither the tree, frequencies, primes nor top giants enter the eventual cutoff. -/
theorem movingSample_topPeriod_progression_range {σ : Type*} (n : ℕ) (C : ℝ) :
    ∀ᶠ L : ℝ in atTop, ∀ (value : σ → ℕ) (hvalue : ∀ i, value i ≠ 0)
      (P V : ℕ), 1 ≤ P → 1 ≤ V → (∀ i, value i ≤ P) →
      (V : ℝ) ≤ Real.exp (C * L) → (P : ℝ) ≤ Real.exp (C * Real.exp ((1 / 100 : ℝ) * L)) →
      ∀ (childBound pivotBound : ℕ → ℕ) (t : FrequencyTree ℤ n)
        (small bulk : TreeLeafTuple (List σ) n) (samples : MovingSampleSlots σ n)
        (hf : (buildMovingSlotData n t small bulk samples).Frequencies (· ≠ 0)),
        (buildMovingSlotData n t small bulk samples).Frequencies (fun s => s.natAbs ≤ V) →
        movingTopPeriod value hvalue childBound pivotBound
          (buildMovingSlotData n t small bulk samples) hf ≤
          ⌊Real.exp (Real.exp ((12 / 1000 : ℝ) * L))⌋₊ := by
  filter_upwards [movingSample_period_exponent_budget n C] with L hL
  intro value hvalue P V hP hV hvalueP hfreqV hprimeP childBound pivotBound t small bulk samples hf hfreq
  apply Nat.le_floor
  exact (movingSample_topPeriod_exp value hvalue P V hP hV hvalueP childBound pivotBound
    n t small bulk samples hf hfreq _ _ hfreqV hprimeP).trans (Real.exp_le_exp.mpr hL)

end Ostmann

end OAI
