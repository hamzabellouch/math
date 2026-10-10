import OAI.Combinatorics.SharpThreshold.BlockSize
import OAI.Combinatorics.SharpThreshold.VarianceConstants

namespace OAI

noncomputable section

namespace Problem313

lemma block_scale_pos {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    0 < Real.sqrt (p * (1 - p)) :=
  Real.sqrt_pos.mpr (mul_pos hp (sub_pos.mpr hp1))

lemma block_scale_le_half (p : ℝ) :
    Real.sqrt (p * (1 - p)) ≤ 1 / 2 := by
  apply Real.sqrt_le_iff.mpr
  constructor
  · norm_num
  · nlinarith [sq_nonneg (p - 1 / 2)]

lemma block_cutoff_pos (n : ℕ) (p : ℝ) (hn : 2 ≤ n)
    (ht : 16 ≤ Real.log (n : ℝ)) (hp : 0 < p) (hp1 : p < 1) :
    0 < Real.sqrt (p * (1 - p)) *
      Real.log (⌊Real.sqrt (n : ℝ)⌋₊ : ℝ) / 64 := by
  have hscale := block_scale_pos hp hp1
  have hlog := log_sqrt_block_lower n hn ht
  have hlogpos : 0 < Real.log (⌊Real.sqrt (n : ℝ)⌋₊ : ℝ) := by linarith
  positivity

lemma block_cutoff_le_log_div_128 (n : ℕ) (p : ℝ) (hn : 2 ≤ n)
    (ht : 16 ≤ Real.log (n : ℝ)) :
    Real.sqrt (p * (1 - p)) *
      Real.log (⌊Real.sqrt (n : ℝ)⌋₊ : ℝ) / 64 ≤ Real.log (n : ℝ) / 128 := by
  have hsize := sqrt_block_size_bounds n hn ht
  have hmpos : 0 < (⌊Real.sqrt (n : ℝ)⌋₊ : ℝ) := by
    exact_mod_cast (by omega : 0 < ⌊Real.sqrt (n : ℝ)⌋₊)
  have hmn : (⌊Real.sqrt (n : ℝ)⌋₊ : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast hsize.2.1
  have hlogupper := Real.log_le_log hmpos hmn
  have hloglower := log_sqrt_block_lower n hn ht
  have hlognonneg : 0 ≤ Real.log (⌊Real.sqrt (n : ℝ)⌋₊ : ℝ) := by linarith
  have hmul := mul_le_mul_of_nonneg_right (block_scale_le_half p) hlognonneg
  linarith

lemma block_cutoff_le_log (n : ℕ) (p : ℝ) (hn : 2 ≤ n)
    (ht : 16 ≤ Real.log (n : ℝ)) :
    Real.sqrt (p * (1 - p)) *
      Real.log (⌊Real.sqrt (n : ℝ)⌋₊ : ℝ) / 64 ≤ Real.log (n : ℝ) := by
  have h := block_cutoff_le_log_div_128 n p hn ht
  linarith

/-- A global logarithmic bound which avoids any large-parameter decay calculus. -/
lemma log_sq_le_sixteen_sqrt (x : ℝ) (hx : 1 ≤ x) :
    (Real.log x) ^ 2 ≤ 16 * Real.sqrt x := by
  have hxpos : 0 < x := by linarith
  have hlog : 0 ≤ Real.log x := Real.log_nonneg hx
  have hlin : Real.log x / 4 ≤ Real.exp (Real.log x / 4) := by
    have h := Real.add_one_le_exp (Real.log x / 4)
    linarith
  have hsquare := pow_le_pow_left₀ (by positivity : 0 ≤ Real.log x / 4) hlin 2
  have hexp : (Real.exp (Real.log x / 4)) ^ 2 = Real.sqrt x := by
    rw [pow_two, ← Real.exp_add]
    have harg : Real.log x / 4 + Real.log x / 4 = Real.log x / 2 := by ring
    rw [harg, Real.exp_half, Real.exp_log hxpos]
  rw [hexp] at hsquare
  nlinarith

/-- The support-size correction in the random block capture estimate. -/
lemma block_cutoff_sq_div_sqrt_le_half (n : ℕ) (p : ℝ) (hn : 2 ≤ n)
    (ht : 16 ≤ Real.log (n : ℝ)) :
    (Real.sqrt (p * (1 - p)) *
      Real.log (⌊Real.sqrt (n : ℝ)⌋₊ : ℝ) / 64) ^ 2 /
        Real.sqrt (n : ℝ) ≤ 1 / 2 := by
  have hcut := block_cutoff_le_log_div_128 n p hn ht
  have hlog := log_sqrt_block_lower n hn ht
  have hlogpos : 0 ≤ Real.log (⌊Real.sqrt (n : ℝ)⌋₊ : ℝ) := by linarith
  have hk : 0 ≤ Real.sqrt (p * (1 - p)) *
      Real.log (⌊Real.sqrt (n : ℝ)⌋₊ : ℝ) / 64 := by positivity
  have htsquare := mul_le_mul hcut hcut hk (by linarith : 0 ≤ Real.log (n : ℝ) / 128)
  have hsqrt := log_sq_le_sixteen_sqrt (n : ℝ) (by exact_mod_cast (by omega : 1 ≤ n))
  have hsqrtpos : 0 < Real.sqrt (n : ℝ) := by positivity
  apply (div_le_iff₀ hsqrtpos).mpr
  nlinarith

/-- The exact pair-correction form needed by uniform block counting. -/
lemma block_cutoff_sq_pair_ratio_le_half (n : ℕ) (p : ℝ) (hn : 2 ≤ n)
    (ht : 16 ≤ Real.log (n : ℝ)) :
    (Real.sqrt (p * (1 - p)) *
      Real.log (⌊Real.sqrt (n : ℝ)⌋₊ : ℝ) / 64) ^ 2 *
        (((⌊Real.sqrt (n : ℝ)⌋₊ : ℝ) - 1) / ((n : ℝ) - 1)) ≤ 1 / 2 := by
  have hratio := sqrt_block_pair_ratio n hn
  have hmul := mul_le_mul_of_nonneg_left hratio
    (sq_nonneg (Real.sqrt (p * (1 - p)) *
      Real.log (⌊Real.sqrt (n : ℝ)⌋₊ : ℝ) / 64))
  have hbound := block_cutoff_sq_div_sqrt_le_half n p hn ht
  rw [mul_one_div] at hmul
  exact hmul.trans hbound

lemma block_support_pair_correction_le_half (n v : ℕ) (p : ℝ) (hn : 2 ≤ n)
    (ht : 16 ≤ Real.log (n : ℝ))
    (hv : (v : ℝ) ≤ (Real.sqrt (p * (1 - p)) *
      Real.log (⌊Real.sqrt (n : ℝ)⌋₊ : ℝ) / 64) ^ 2) :
    ((v : ℝ) - 1) *
        (((⌊Real.sqrt (n : ℝ)⌋₊ : ℝ) - 1) / ((n : ℝ) - 1)) ≤ 1 / 2 := by
  have hsize := sqrt_block_size_bounds n hn ht
  have hm : (3 : ℝ) ≤ (⌊Real.sqrt (n : ℝ)⌋₊ : ℝ) := by exact_mod_cast hsize.1
  have hnreal : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hratio : 0 ≤ ((⌊Real.sqrt (n : ℝ)⌋₊ : ℝ) - 1) / ((n : ℝ) - 1) := by
    apply div_nonneg <;> linarith
  have hv' : (v : ℝ) - 1 ≤ (Real.sqrt (p * (1 - p)) *
      Real.log (⌊Real.sqrt (n : ℝ)⌋₊ : ℝ) / 64) ^ 2 := by linarith
  exact (mul_le_mul_of_nonneg_right hv' hratio).trans
    (block_cutoff_sq_pair_ratio_le_half n p hn ht)

/-- The full numerical coefficient for the actual square-root block parameters. -/
theorem graph_block_preconstant_bound (n : ℕ) (p : ℝ) (hn : 2 ≤ n)
    (ht : 16 ≤ Real.log (n : ℝ)) (hp : 0 < p) (hp1 : p < 1) :
    4 * (⌊Real.sqrt (n : ℝ)⌋₊ : ℝ) ^ (-(1 : ℝ) / 4) +
        2 * (Real.sqrt (p * (1 - p))) ^ 2 /
          (Real.sqrt (p * (1 - p)) *
            Real.log (⌊Real.sqrt (n : ℝ)⌋₊ : ℝ) / 64) ^ 2 ≤
      (2 : ℝ) ^ 17 / (Real.log (n : ℝ)) ^ 2 := by
  have hsize := sqrt_block_size_bounds n hn ht
  exact variance_constant_bound (by linarith)
    (by exact_mod_cast (by omega : 0 < ⌊Real.sqrt (n : ℝ)⌋₊))
    (log_sqrt_block_lower n hn ht) (block_scale_pos hp hp1)

/-- The elementary coefficient comparison in the small-logarithm branch. -/
theorem small_log_poincare_coefficient (n : ℕ) (p : ℝ) (hn : 2 ≤ n)
    (ht : Real.log (n : ℝ) ≤ 16) :
    p * (1 - p) ≤ (2 : ℝ) ^ 17 / (Real.log (n : ℝ)) ^ 2 := by
  have hnreal : (1 : ℝ) < n := by exact_mod_cast (by omega : 1 < n)
  have hlogpos := Real.log_pos hnreal
  have hvar : p * (1 - p) ≤ 1 / 4 := by nlinarith [sq_nonneg (p - 1 / 2)]
  apply hvar.trans
  apply (le_div_iff₀ (sq_pos_of_pos hlogpos)).mpr
  have hsquare := mul_le_mul ht ht hlogpos.le (by norm_num : (0 : ℝ) ≤ 16)
  norm_num at hsquare ⊢
  nlinarith

end Problem313

end

end OAI
