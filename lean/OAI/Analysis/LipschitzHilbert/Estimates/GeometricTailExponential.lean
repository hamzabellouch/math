import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.MeasureTheory.Measure.Real

namespace OAI

/-! A geometric distribution bound gives an exponential moment by summing
the level strips. The factor is absolute and no boundedness hypothesis is
needed for the function. -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace LipschitzHilbert

theorem geometric_tail_exponential {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] (f : X → ℝ) (hf : Measurable f)
    (hf0 : ∀ x, 0 ≤ f x) {H : ℝ} (hH : 0 < H)
    (htail : ∀ n : ℕ, μ.real {x | (n : ℝ) * H < f x} ≤
      (1 / 2 : ℝ) ^ n * μ.real univ) :
    (∫⁻ x, ENNReal.ofReal ((3 / 2 : ℝ) ^ (f x / H)) ∂μ) ≤ 7 * μ univ := by
  classical
  let S := fun n : ℕ => {x | (n : ℝ) * H < f x}
  let F := fun n : ℕ => (S n).indicator (fun _ => (3 / 2 : ℝ≥0∞) ^ (n + 1))
  have hSm (n : ℕ) : MeasurableSet (S n) := measurableSet_lt measurable_const hf
  have hFm (n : ℕ) : Measurable (F n) := measurable_const.indicator (hSm n)
  have hpoint (x : X) : ENNReal.ofReal ((3 / 2 : ℝ) ^ (f x / H)) ≤ 1 + ∑' n, F n x := by
    by_cases hx : f x = 0
    · simp [hx]
    · have hfx : 0 < f x := lt_of_le_of_ne (hf0 x) (Ne.symm hx)
      have hk : 0 < ⌈f x / H⌉₊ := Nat.ceil_pos.mpr (div_pos hfx hH)
      let n := ⌈f x / H⌉₊ - 1
      have hn : n + 1 = ⌈f x / H⌉₊ := by dsimp [n]; omega
      have hns : x ∈ S n := by
        apply (lt_div_iff₀ hH).mp
        apply Nat.lt_ceil.mp
        dsimp [n]
        omega
      have hr : (3 / 2 : ℝ) ^ (f x / H) ≤ (3 / 2 : ℝ) ^ (n + 1) := by
        rw [← Real.rpow_natCast]
        apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
        rw [hn]
        exact Nat.le_ceil _
      have hterm : ENNReal.ofReal ((3 / 2 : ℝ) ^ (f x / H)) ≤ F n x := by
        dsimp only [F]
        rw [indicator_of_mem hns]
        have h := ENNReal.ofReal_le_ofReal hr
        simpa only [ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 3 / 2),
          ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2),
          ENNReal.ofReal_ofNat] using h
      have hsum : F n x ≤ ∑' j, F j x := ENNReal.le_tsum (f := fun j => F j x) n
      exact hterm.trans (hsum.trans le_add_self)
  have ht (n : ℕ) : μ (S n) ≤ (1 / 2 : ℝ≥0∞) ^ n * μ univ := by
    have h := ENNReal.ofReal_le_ofReal (htail n)
    rw [ofReal_measureReal, ENNReal.ofReal_mul (pow_nonneg (by norm_num) _),
      ofReal_measureReal] at h
    norm_num only [ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 1 / 2),
      ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2), ENNReal.ofReal_one,
      ENNReal.ofReal_ofNat] at h
    exact h
  calc
    _ ≤ ∫⁻ x, 1 + ∑' n, F n x ∂μ := lintegral_mono hpoint
    _ = μ univ + ∑' n, ∫⁻ x, F n x ∂μ := by
      rw [lintegral_add_left measurable_const, lintegral_const, one_mul,
        lintegral_tsum (fun n => (hFm n).aemeasurable)]
    _ = μ univ + ∑' n, (3 / 2 : ℝ≥0∞) ^ (n + 1) * μ (S n) := by
      congr 1
      apply tsum_congr
      intro n
      exact lintegral_indicator_const (hSm n) _
    _ ≤ μ univ + ∑' n, (3 / 2 : ℝ≥0∞) ^ (n + 1) * ((1 / 2 : ℝ≥0∞) ^ n * μ univ) := by
      gcongr with n
      exact ht n
    _ = μ univ + (3 / 2 : ℝ≥0∞) * (∑' n : ℕ, (3 / 4 : ℝ≥0∞) ^ n) * μ univ := by
      rw [← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_right]
      congr 1
      apply tsum_congr
      intro n
      rw [pow_succ]
      have hp : (3 / 4 : ℝ≥0∞) ^ n = (3 / 2 : ℝ≥0∞) ^ n * (1 / 2 : ℝ≥0∞) ^ n := by
        rw [← mul_pow]
        congr 1
        have hnn : (3 / 4 : ℝ≥0) = (3 / 2 : ℝ≥0) * (1 / 2 : ℝ≥0) := by norm_num
        have hc := congrArg (fun z : ℝ≥0 => (z : ℝ≥0∞)) hnn
        simpa only [ENNReal.coe_mul, ENNReal.coe_div (by norm_num : (4 : ℝ≥0) ≠ 0),
          ENNReal.coe_div (by norm_num : (2 : ℝ≥0) ≠ 0), ENNReal.coe_ofNat,
          ENNReal.coe_one] using hc
      rw [hp]
      ring
    _ = 7 * μ univ := by
      rw [ENNReal.tsum_geometric]
      have hc : (3 / 2 : ℝ≥0∞) * (1 - 3 / 4)⁻¹ = 6 := by
        have hquarter : (1 - 3 / 4 : ℝ≥0) = 1 / 4 := by
          apply NNReal.eq
          rw [NNReal.coe_sub (by exact_mod_cast (show (3 / 4 : ℝ) ≤ 1 by norm_num))]
          norm_num
        have hne : (1 - 3 / 4 : ℝ≥0) ≠ 0 := by rw [hquarter]; norm_num
        have hnn : (3 / 2 : ℝ≥0) * (1 - 3 / 4)⁻¹ = 6 := by rw [hquarter]; norm_num
        have hc := congrArg (fun z : ℝ≥0 => (z : ℝ≥0∞)) hnn
        simpa only [ENNReal.coe_mul, ENNReal.coe_inv hne,
          ENNReal.coe_sub, ENNReal.coe_div (by norm_num : (4 : ℝ≥0) ≠ 0),
          ENNReal.coe_div (by norm_num : (2 : ℝ≥0) ≠ 0), ENNReal.coe_ofNat,
          ENNReal.coe_one] using hc
      calc
        _ = (1 + (3 / 2 : ℝ≥0∞) * (1 - 3 / 4)⁻¹) * μ univ := by ring
        _ = _ := by rw [hc]; norm_num

end LipschitzHilbert

end

end OAI
