import Mathlib

namespace OAI

universe u

noncomputable section

namespace Problem313

/-- Uniform bias-dependent logarithmic bound used in the low-degree estimate. -/
theorem sigma_mul_log_four_div_le_two {σ : ℝ} (hσ : 0 < σ)
    (hσhalf : σ ≤ 1 / 2) : σ * Real.log (4 / σ) ≤ 2 := by
  have hσne : σ ≠ 0 := ne_of_gt hσ
  have hlog2 : Real.log (2 : ℝ) ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have hinv : 0 < 1 / (2 * σ) := by positivity
  have hloginv := Real.log_le_sub_one_of_pos hinv
  have hlogsplit : Real.log (4 / σ) =
      3 * Real.log 2 + Real.log (1 / (2 * σ)) := by
    rw [Real.log_div (by norm_num) hσne,
      Real.log_div (by norm_num) (by positivity : 2 * σ ≠ 0),
      Real.log_mul (by norm_num) hσne]
    have hlog4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
      have := Real.log_pow (2 : ℝ) 2
      norm_num at this
      exact this
    rw [hlog4, Real.log_one]
    ring
  have hscaled := mul_le_mul_of_nonneg_left hloginv (le_of_lt hσ)
  have hcancel : σ * (1 / (2 * σ) - 1) = 1 / 2 - σ := by
    field_simp
  rw [hcancel] at hscaled
  rw [hlogsplit]
  nlinarith [mul_le_mul_of_nonneg_left hlog2 (le_of_lt hσ)]

/-- The noise loss has a uniformly small power of the orbit-size parameter. -/
theorem noise_loss_le_rpow {σ m : ℝ} (hσ : 0 < σ)
    (hσhalf : σ ≤ 1 / 2) (hm : 1 ≤ m) :
    (σ / 4) ^ (-(2 : ℝ) * (σ * Real.log m / 64)) ≤ m ^ (1 / 16 : ℝ) := by
  have hmpos : 0 < m := lt_of_lt_of_le zero_lt_one hm
  have hlogm : 0 ≤ Real.log m := Real.log_nonneg hm
  have hσne : σ ≠ 0 := ne_of_gt hσ
  have hlogneg : Real.log (σ / 4) = -Real.log (4 / σ) := by
    rw [Real.log_div hσne (by norm_num), Real.log_div (by norm_num) hσne]
    ring
  rw [Real.rpow_def_of_pos (by positivity : 0 < σ / 4),
    Real.rpow_def_of_pos hmpos]
  apply Real.exp_le_exp.mpr
  rw [hlogneg]
  have hbound := sigma_mul_log_four_div_le_two hσ hσhalf
  have hmul := mul_le_mul_of_nonneg_right hbound hlogm
  nlinarith

/-- Absorb the residual quarter-variance factor and the stronger exponent. -/
theorem sigma_sq_mul_rpow_le {σ m : ℝ} (hσ : 0 ≤ σ)
    (hσhalf : σ ≤ 1 / 2) (hm : 1 ≤ m) :
    σ ^ 2 * m ^ (-5 / 16 : ℝ) ≤ m ^ (-1 / 4 : ℝ) := by
  have hσsq : σ ^ 2 ≤ 1 := by nlinarith
  have hmpos : 0 < m := lt_of_lt_of_le zero_lt_one hm
  calc
    σ ^ 2 * m ^ (-5 / 16 : ℝ) ≤ 1 * m ^ (-5 / 16 : ℝ) :=
      mul_le_mul_of_nonneg_right hσsq (Real.rpow_nonneg (le_of_lt hmpos) _)
    _ = m ^ (-5 / 16 : ℝ) := one_mul _
    _ ≤ m ^ (-1 / 4 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hm (by norm_num)

/-- An individual influence contributes a small extra factor when total influence is small. -/
theorem influence_three_halves_le {a I m : ℝ} (ha : 0 ≤ a) (hm : 1 ≤ m)
    (hai : a ≤ I / m) (hI : I ≤ m ^ (1 / 4 : ℝ)) :
    a ^ (3 / 2 : ℝ) ≤ m ^ (-3 / 8 : ℝ) * a := by
  have hmpos : 0 < m := lt_of_lt_of_le zero_lt_one hm
  have hpow : m ^ (-3 / 4 : ℝ) * m = m ^ (1 / 4 : ℝ) := by
    calc
      m ^ (-3 / 4 : ℝ) * m = m ^ (-3 / 4 : ℝ) * m ^ (1 : ℝ) := by
        rw [Real.rpow_one]
      _ = m ^ ((-3 / 4 : ℝ) + 1) := (Real.rpow_add hmpos _ _).symm
      _ = m ^ (1 / 4 : ℝ) := by norm_num
  have hratio : I / m ≤ m ^ (-3 / 4 : ℝ) := by
    apply (div_le_iff₀ hmpos).2
    rwa [hpow]
  have hhalf : a ^ (1 / 2 : ℝ) ≤ m ^ (-3 / 8 : ℝ) := by
    have h := Real.rpow_le_rpow ha (hai.trans hratio) (by norm_num : (0 : ℝ) ≤ 1 / 2)
    rw [← Real.rpow_mul (le_of_lt hmpos)] at h
    norm_num at h ⊢
    exact h
  have hsplit : a ^ (3 / 2 : ℝ) = a * a ^ (1 / 2 : ℝ) := by
    have h := Real.rpow_add_of_nonneg ha (by norm_num : (0 : ℝ) ≤ 1)
      (by norm_num : (0 : ℝ) ≤ 1 / 2)
    norm_num at h
    exact h
  rw [hsplit, mul_comm (m ^ _) a]
  exact mul_le_mul_of_nonneg_left hhalf ha

/-- Sum the individual three-halves estimate without a cardinality loss. -/
theorem sum_influence_three_halves_le {ι : Type u} (s : Finset ι) (a : ι → ℝ)
    {m : ℝ} (hm : 1 ≤ m) (ha : ∀ i ∈ s, 0 ≤ a i)
    (horbit : ∀ i ∈ s, a i ≤ (∑ j ∈ s, a j) / m)
    (hsmall : (∑ j ∈ s, a j) ≤ m ^ (1 / 4 : ℝ)) :
    (∑ i ∈ s, a i ^ (3 / 2 : ℝ)) ≤ m ^ (-3 / 8 : ℝ) * (∑ i ∈ s, a i) := by
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun i hi =>
    influence_three_halves_le (ha i hi) hm (horbit i hi) hsmall

end Problem313

end

end OAI
