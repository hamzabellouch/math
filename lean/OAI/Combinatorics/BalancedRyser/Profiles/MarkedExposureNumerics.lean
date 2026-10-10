import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic
import OAI.Combinatorics.BalancedRyser.Profiles.MarkedExposure

namespace OAI

namespace Balanced.MarkedExposureNumerics

open scoped BigOperators ENNReal Classical
open MeasureTheory

noncomputable def exponentialCost (A B ξ : ℝ) : ℝ :=
  A * Real.log 2 + (1 + ξ) * Real.log (max 1 B)

theorem two_pow_mul_pow_le (q m N r : ℕ) (A B ξ : ℝ)
    (hq : 1 ≤ q) (hB : 0 ≤ B) (hBq : max 1 B ≤ (q : ℝ))
    (hm : m ≤ q) (hN : (N : ℝ) ≤ A * q)
    (hr : (m : ℝ) + ξ * q ≤ r) :
    (2 : ℝ) ^ N * (B / q) ^ r ≤
      Real.exp (exponentialCost A B ξ * q - ξ * q * Real.log q) / (q : ℝ) ^ m := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  let b : ℝ := max 1 B
  have hb : 0 < b := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hbq : b / q ≤ 1 := (div_le_one hqR).mpr hBq
  have hbl : 0 ≤ Real.log b := Real.log_nonneg (le_max_left _ _)
  have h2l : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hmr : (m : ℝ) ≤ q := by exact_mod_cast hm
  have hbase : (B / (q : ℝ)) ^ r ≤ (b / q) ^ r := by
    gcongr
    exact le_max_right _ _
  have hexponent :
      (N : ℝ) * Real.log 2 + Real.log (b / q) * ((m : ℝ) + ξ * q) ≤
        exponentialCost A B ξ * q - ξ * q * Real.log q -
          (m : ℝ) * Real.log q := by
    rw [Real.log_div hb.ne' hqR.ne']
    have h1 := mul_le_mul_of_nonneg_right hN h2l
    have h2 := mul_le_mul_of_nonneg_right hmr hbl
    dsimp [exponentialCost, b] at *
    nlinarith
  calc
    (2 : ℝ) ^ N * (B / q) ^ r ≤ (2 : ℝ) ^ N * (b / q) ^ r := by
      exact mul_le_mul_of_nonneg_left hbase (by positivity)
    _ ≤ (2 : ℝ) ^ N * (b / q) ^ ((m : ℝ) + ξ * q) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      rw [← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_ge (div_pos hb hqR) hbq hr
    _ = Real.exp ((N : ℝ) * Real.log 2 +
        Real.log (b / q) * ((m : ℝ) + ξ * q)) := by
      rw [Real.rpow_def_of_pos (div_pos hb hqR), Real.exp_add,
        Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    _ ≤ Real.exp (exponentialCost A B ξ * q - ξ * q * Real.log q -
        (m : ℝ) * Real.log q) := Real.exp_le_exp.mpr hexponent
    _ = _ := by
      rw [Real.exp_sub, Real.exp_nat_mul, Real.exp_log hqR]

theorem exposure_length_le (k q m : ℕ) (hq : 1 ≤ q) (hm : m ≤ q) :
    ((k * (q + 1) + m : ℕ) : ℝ) ≤ (2 * (k : ℝ) + 1) * q := by
  have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hmR : (m : ℝ) ≤ q := by exact_mod_cast hm
  push_cast
  nlinarith [mul_le_mul_of_nonneg_left hqR (show (0 : ℝ) ≤ k by positivity)]

theorem atLeast_ceil_eq {Ω ι : Type*} (s : Finset ι) (E : ι → Set Ω) (a : ℝ) :
    MarkedExposure.atLeast s E ⌈a⌉₊ =
      {ω | a ≤ ((s.filter fun i => ω ∈ E i).card : ℝ)} := by
  classical
  ext ω
  exact Nat.ceil_le

theorem rare_mark_bound_of_step {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (E : ℕ → Set Ω)
    (k q m : ℕ) (B ξ : ℝ) (hq : 1 ≤ q) (hB : 0 ≤ B)
    (hBq : max 1 B ≤ (q : ℝ)) (hm : m ≤ q)
    (hstep : ∀ j < k * (q + 1) + m, ∀ t : Finset ℕ,
      t ⊆ Finset.range j → μ (E j ∩ (⋂ i ∈ t, E i)) ≤
        ENNReal.ofReal (B / q) * μ (⋂ i ∈ t, E i)) :
    μ.real (MarkedExposure.atLeast (Finset.range (k * (q + 1) + m)) E
        ⌈(m : ℝ) + ξ * q⌉₊) ≤
      Real.exp (exponentialCost (2 * k + 1) B ξ * q - ξ * q * Real.log q) /
        (q : ℝ) ^ m := by
  have h := MarkedExposure.tail_le_two_pow_mul_of_step μ E
    (k * (q + 1) + m) ⌈(m : ℝ) + ξ * q⌉₊ (ENNReal.ofReal (B / q)) hstep
  have hreal := ENNReal.toReal_mono (by finiteness) h
  have hweight : 0 ≤ B / (q : ℝ) := div_nonneg hB (by positivity)
  simp only [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofNat,
    ENNReal.toReal_ofReal hweight] at hreal
  exact hreal.trans (two_pow_mul_pow_le q m (k * (q + 1) + m)
    ⌈(m : ℝ) + ξ * q⌉₊ (2 * k + 1) B ξ hq hB hBq hm
    (exposure_length_le k q m hq hm) (Nat.le_ceil _))

theorem uniform_detection_constant (k q : ℕ) (ξ : ℝ)
    (hk : 1 ≤ k) (hq : 1 ≤ q) (hξ : 0 ≤ ξ) :
    ξ / (4 * k) ≤ ξ * q / (2 * ((k : ℝ) * (q + 1))) := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  have hx := mul_nonneg hξ (sub_nonneg.mpr hqR)
  nlinarith [mul_nonneg hkR.le hx]

end Balanced.MarkedExposureNumerics

end OAI
