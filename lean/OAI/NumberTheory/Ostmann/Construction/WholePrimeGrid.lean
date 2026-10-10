import OAI.NumberTheory.Ostmann.Construction.PrimeGridSupport
import OAI.NumberTheory.Ostmann.Arithmetic.ArithmeticErrorRates

namespace OAI

/-! # Exact short-cell partitions of the original whole prime shells -/

namespace Ostmann
open Filter
open scoped Classical

noncomputable def wholePrimeGridCount (b : ℝ) : ℕ := ⌈Real.exp (b + 1)⌉₊ + 1

theorem wholePrimeGridCount_pos (b : ℝ) : 0 < wholePrimeGridCount b := by
  unfold wholePrimeGridCount
  omega

theorem wholePrimeGridCount_upper (b : ℝ) :
    (wholePrimeGridCount b : ℝ) ≤ Real.exp (b + 1) + 2 := by
  have h := Nat.ceil_lt_add_one (Real.exp_nonneg (b + 1))
  unfold wholePrimeGridCount
  push_cast
  linarith

theorem wholePrimeGridCount_width {a b : ℝ} (hab : a ≤ b) :
    Real.exp (a + 1) - Real.exp a ≤ (wholePrimeGridCount b : ℝ) := by
  have he : Real.exp (a + 1) ≤ Real.exp (b + 1) := Real.exp_le_exp.mpr (by linarith)
  have hc := Nat.le_ceil (Real.exp (b + 1))
  unfold wholePrimeGridCount
  push_cast
  linarith [Real.exp_pos a]

theorem interval_grid_width {N : ℕ} (hN : 0 < N) {u v : ℝ}
    (huv : u ≤ v) (hwidth : v - u ≤ (N : ℝ)) :
    0 ≤ (v - u) / (N : ℝ) ∧ (v - u) / (N : ℝ) ≤ 1 ∧
      u + (N : ℝ) * ((v - u) / (N : ℝ)) = v := by
  have hp : (0 : ℝ) < N := by exact_mod_cast hN
  refine ⟨div_nonneg (sub_nonneg.mpr huv) hp.le, ?_, ?_⟩
  · exact (div_le_one hp).mpr hwidth
  · rw [mul_div_cancel₀ _ hp.ne']
    ring

/-- The mesh covers the entire original shell, including every boundary
prime allowed by its left-open, right-closed convention. -/
theorem whole_prime_grid_support (q : ℕ) [NeZero q] (a b : ℝ)
    (hab : a ≤ b) (hq : (q : ℝ) ≤ Real.exp (Real.exp a)) :
    let N := wholePrimeGridCount b
    let h := (Real.exp (a + 1) - Real.exp a) / (N : ℝ)
    primeCellSupport q (gridResidue (N := N) (q := q))
      (gridLower (Real.exp a) h) (gridUpper (Real.exp a) h) =
        primeLogCellSet 1 0 (Real.exp a) (Real.exp (a + 1)) := by
  intro N h
  have hp := interval_grid_width (wholePrimeGridCount_pos b)
    (Real.exp_le_exp.mpr (by linarith : a ≤ a + 1)) (wholePrimeGridCount_width hab)
  ext p
  rw [mem_gridPrimeSupport_iff_prime N q (Real.exp a) h hp.1 hq,
    mem_primeLogCellSet_iff]
  rw [show Real.exp a + N * h = Real.exp (a + 1) from hp.2.2]
  simp only [Nat.modEq_one, true_and]

/-- A whole shell of arbitrary log-log width has the same exact finite grid.
The mesh size depends on the upper endpoint, not on a unit-width restriction. -/
theorem whole_interval_prime_grid_support (q : ℕ) [NeZero q] (a b : ℝ)
    (hab : a ≤ b) (hq : (q : ℝ) ≤ Real.exp (Real.exp a)) :
    let N := wholePrimeGridCount b
    let h := (Real.exp b - Real.exp a) / (N : ℝ)
    primeCellSupport q (gridResidue (N := N) (q := q))
      (gridLower (Real.exp a) h) (gridUpper (Real.exp a) h) =
        primeLogCellSet 1 0 (Real.exp a) (Real.exp b) := by
  intro N h
  have hwidth : Real.exp b - Real.exp a ≤ (wholePrimeGridCount b : ℝ) := by
    have hc := Nat.le_ceil (Real.exp (b + 1))
    have he : Real.exp b ≤ Real.exp (b + 1) := Real.exp_le_exp.mpr (by linarith)
    unfold wholePrimeGridCount
    push_cast
    linarith [Real.exp_pos a]
  have hp := interval_grid_width (wholePrimeGridCount_pos b)
    (Real.exp_le_exp.mpr hab) hwidth
  ext p
  rw [mem_gridPrimeSupport_iff_prime N q (Real.exp a) h hp.1 hq,
    mem_primeLogCellSet_iff]
  rw [show Real.exp a + N * h = Real.exp b from hp.2.2]
  simp only [Nat.modEq_one, true_and]

/-- The coarse partition is enough because the sharp real kernel is
integrated exactly on each cell. Its count is far below the cell budget. -/
theorem wholePrimeGridCount_eventual (K : ℝ) (hK : 0 ≤ K) :
    ∀ᶠ L : ℝ in atTop, ∀ b : ℝ, b ≤ K * L →
      (wholePrimeGridCount b : ℝ) ≤ Real.exp (Real.exp ((14 / 10000 : ℝ) * L)) := by
  filter_upwards [arithmetic_exponent_absorption 0 (14 / 10000) 0 (K + 3) 1 1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    eventually_ge_atTop (1 : ℝ)] with L hrate hL
  intro b hb
  have hL0 : 0 ≤ L := by linarith
  have hCL0 : 0 ≤ K * L := mul_nonneg hK hL0
  have hscale : K * L + 3 ≤ Real.exp ((14 / 10000 : ℝ) * L) := by
    simp only [zero_mul, Real.exp_zero, mul_one, pow_one] at hrate
    nlinarith
  have hthree : (3 : ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp 2]
  have hunit : 1 ≤ Real.exp (K * L + 1) := Real.one_le_exp_iff.mpr (by linarith)
  calc
    _ ≤ Real.exp (b + 1) + 2 := wholePrimeGridCount_upper b
    _ ≤ Real.exp (K * L + 1) + 2 := by
      have he : Real.exp (b + 1) ≤ Real.exp (K * L + 1) := Real.exp_le_exp.mpr (by linarith)
      linarith
    _ ≤ 3 * Real.exp (K * L + 1) := by linarith
    _ ≤ Real.exp 2 * Real.exp (K * L + 1) :=
      mul_le_mul_of_nonneg_right hthree (Real.exp_nonneg _)
    _ = Real.exp (K * L + 3) := by rw [← Real.exp_add]; congr 1; ring
    _ ≤ _ := Real.exp_le_exp.mpr hscale

end Ostmann

end OAI
