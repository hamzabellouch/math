import Mathlib

namespace OAI

noncomputable section

namespace Problem313

theorem half_le_nat_floor {x : ℝ} (hx : 2 ≤ x) :
    x / 2 ≤ (⌊x⌋₊ : ℝ) := by
  have hfloor := Nat.sub_one_lt_floor x
  linarith

/-- Elementary size estimates for the square-root vertex block. -/
theorem sqrt_block_size_bounds (n : ℕ) (hn : 2 ≤ n)
    (ht : 16 ≤ Real.log (n : ℝ)) :
    3 ≤ ⌊Real.sqrt (n : ℝ)⌋₊ ∧
      ⌊Real.sqrt (n : ℝ)⌋₊ ≤ n ∧
      Real.sqrt (n : ℝ) / 2 ≤ (⌊Real.sqrt (n : ℝ)⌋₊ : ℝ) := by
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hnlarge : 17 ≤ (n : ℝ) := by
    have := Real.log_le_sub_one_of_pos hnpos
    linarith
  have hsqrt : 4 ≤ Real.sqrt (n : ℝ) :=
    (Real.le_sqrt (by norm_num) (le_of_lt hnpos)).2 (by linarith)
  refine ⟨Nat.le_floor (by norm_num; linarith), ?_, half_le_nat_floor (by linarith)⟩
  apply Nat.floor_le_of_le
  apply Real.sqrt_le_iff.mpr
  constructor
  · positivity
  · nlinarith

/-- The square-root block retains at least one third of the original logarithm. -/
theorem log_sqrt_block_lower (n : ℕ) (hn : 2 ≤ n)
    (ht : 16 ≤ Real.log (n : ℝ)) :
    Real.log (n : ℝ) / 3 ≤ Real.log (⌊Real.sqrt (n : ℝ)⌋₊ : ℝ) := by
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hsqrtpos : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hnpos
  have hhalf := (sqrt_block_size_bounds n hn ht).2.2
  have hlog := Real.log_le_log (by positivity : 0 < Real.sqrt (n : ℝ) / 2) hhalf
  rw [Real.log_div (ne_of_gt hsqrtpos) (by norm_num),
    Real.log_sqrt (le_of_lt hnpos)] at hlog
  have htwo : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  linarith

/-- Pair-inclusion correction for the square-root-sized uniform block. -/
theorem sqrt_block_pair_ratio (n : ℕ) (hn : 2 ≤ n) :
    ((⌊Real.sqrt (n : ℝ)⌋₊ : ℝ) - 1) / ((n : ℝ) - 1) ≤
      1 / Real.sqrt (n : ℝ) := by
  have hnreal : 2 ≤ (n : ℝ) := by exact_mod_cast hn
  have hnpos : 0 < (n : ℝ) := by linarith
  have hsqrtpos : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hnpos
  have hsqrtone : 1 ≤ Real.sqrt (n : ℝ) :=
    (Real.le_sqrt (by norm_num) (le_of_lt hnpos)).2 (by linarith)
  have hfloor := Nat.floor_le (Real.sqrt_nonneg (n : ℝ))
  have hprod := mul_le_mul_of_nonneg_right hfloor (le_of_lt hsqrtpos)
  have hsquare := Real.sq_sqrt (le_of_lt hnpos)
  apply (div_le_div_iff₀ (by linarith : 0 < (n : ℝ) - 1) hsqrtpos).2
  nlinarith

/-- A coarse exponential estimate sufficient for the block-capture union bound. -/
theorem block_capture_exp_lower (t : ℝ) (ht : 16 ≤ t) :
    2 * t ^ 2 ≤ Real.exp (t / 2) := by
  have htpos : 0 ≤ t := by linarith
  have hsq : 16 * t ≤ t ^ 2 := by
    nlinarith [mul_nonneg htpos (sub_nonneg.mpr ht)]
  have hcube : 256 * t ≤ t ^ 3 := by
    calc
      256 * t ≤ 16 * t ^ 2 := by linarith
      _ ≤ t * t ^ 2 := mul_le_mul_of_nonneg_right ht (sq_nonneg t)
      _ = t ^ 3 := by ring
  have hexp := Real.sum_le_exp_of_nonneg (by positivity : 0 ≤ t / 4) 4
  norm_num [Finset.sum_range_succ, Nat.factorial] at hexp
  have hlower : (17 / 12 : ℝ) * t ≤ Real.exp (t / 4) := by
    nlinarith
  have hsquare : ((17 / 12 : ℝ) * t) ^ 2 ≤ (Real.exp (t / 4)) ^ 2 :=
    pow_le_pow_left₀ (by positivity) hlower 2
  have hid : Real.exp (t / 2) = (Real.exp (t / 4)) ^ 2 := by
    rw [show t / 2 = t / 4 + t / 4 by ring, Real.exp_add]
    ring
  rw [hid]
  nlinarith [sq_nonneg t]

theorem block_capture_decay (t : ℝ) (ht : 16 ≤ t) :
    t ^ 2 * Real.exp (-t / 2) ≤ (1 / 2 : ℝ) := by
  rw [show -t / 2 = -(t / 2) by ring, Real.exp_neg,
    ← div_eq_mul_inv]
  apply (div_le_iff₀ (Real.exp_pos (t / 2))).2
  have := block_capture_exp_lower t ht
  linarith

theorem log_square_div_sqrt_le_half (n : ℕ) (hn : 2 ≤ n)
    (ht : 16 ≤ Real.log (n : ℝ)) :
    (Real.log (n : ℝ)) ^ 2 / Real.sqrt (n : ℝ) ≤ (1 / 2 : ℝ) := by
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have h := block_capture_exp_lower (Real.log (n : ℝ)) ht
  rw [Real.exp_half, Real.exp_log hnpos] at h
  apply (div_le_iff₀ (Real.sqrt_pos.2 hnpos)).2
  linarith

/-- The numerical loss in the singleton-capture union bound is at most one half. -/
theorem sqrt_block_capture_correction (n : ℕ) (v : ℝ) (hn : 2 ≤ n)
    (ht : 16 ≤ Real.log (n : ℝ)) (hvone : 1 ≤ v)
    (hv : v ≤ (Real.log (n : ℝ)) ^ 2) :
    (v - 1) * (((⌊Real.sqrt (n : ℝ)⌋₊ : ℝ) - 1) / ((n : ℝ) - 1)) ≤
      (1 / 2 : ℝ) := by
  calc
    (v - 1) * (((⌊Real.sqrt (n : ℝ)⌋₊ : ℝ) - 1) / ((n : ℝ) - 1))
        ≤ (v - 1) * (1 / Real.sqrt (n : ℝ)) :=
      mul_le_mul_of_nonneg_left (sqrt_block_pair_ratio n hn) (by linarith)
    _ ≤ (Real.log (n : ℝ)) ^ 2 * (1 / Real.sqrt (n : ℝ)) :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    _ = (Real.log (n : ℝ)) ^ 2 / Real.sqrt (n : ℝ) := by ring
    _ ≤ 1 / 2 := log_square_div_sqrt_le_half n hn ht

end Problem313

end

end OAI
