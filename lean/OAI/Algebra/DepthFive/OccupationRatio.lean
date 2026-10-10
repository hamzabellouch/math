import Mathlib

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem335

/-- The elementary logarithmic lower bound used for factorial moment ratios. -/
theorem log_one_sub_ge_neg_two_mul {x : ℝ} (hx : 0 ≤ x) (hxhalf : x ≤ 1 / 2) :
    -2 * x ≤ Real.log (1 - x) := by
  have hpos : 0 < 1 - x := by linarith
  have hinv : (1 - x)⁻¹ ≤ 1 + 2 * x := by
    rw [inv_eq_one_div, div_le_iff₀ hpos]
    nlinarith [mul_nonneg hx (show 0 ≤ 1 - 2 * x by linarith)]
  have hlog := Real.one_sub_inv_le_log_of_pos hpos
  linarith

/-- A single factor of the occupation ratio has an exponential lower bound. -/
theorem exp_le_occupation_factor {x y : ℝ}
    (hx : 0 ≤ x) (hxhalf : x ≤ 1 / 2) (hy : 0 ≤ y) :
    Real.exp (-2 * x - y) ≤ (1 - x) / (1 + y) := by
  have hxpos : 0 < 1 - x := by linarith
  have hypos : 0 < 1 + y := by linarith
  have hlower := log_one_sub_ge_neg_two_mul hx hxhalf
  have hupper := Real.log_le_sub_one_of_pos hypos
  have hlog : -2 * x - y ≤ Real.log ((1 - x) / (1 + y)) := by
    rw [Real.log_div (ne_of_gt hxpos) (ne_of_gt hypos)]
    linarith
  exact (Real.le_log_iff_exp_le (div_pos hxpos hypos)).mp hlog

/-- The finite product appearing when a composition factorial moment is normalized
by the independent geometric factorial moment. -/
def occupationRatio (t r : ℝ) (H : ℕ) : ℝ :=
  ∏ j ∈ Finset.range H, (1 - (j : ℝ) / t) / (1 + (j : ℝ) / r)

private theorem sum_range_cast_le_half_sq (H : ℕ) :
    (∑ j ∈ Finset.range H, (j : ℝ)) ≤ (H : ℝ) ^ 2 / 2 := by
  induction H with
  | zero => simp
  | succ H ih =>
    rw [Finset.sum_range_succ]
    push_cast
    nlinarith

/-- Uniform upper bound for the occupation ratio. -/
theorem occupationRatio_le_one {t r : ℝ} {H : ℕ}
    (ht : 0 < t) (hr : 0 < r) (hH : (H : ℝ) ≤ t) :
    occupationRatio t r H ≤ 1 := by
  apply Finset.prod_le_one₀
  · intro j hj
    have hjH : (j : ℝ) ≤ H := by exact_mod_cast (Finset.mem_range.mp hj).le
    have hjt : (j : ℝ) / t ≤ 1 := (div_le_one ht).2 (hjH.trans hH)
    apply div_nonneg (by linarith)
    positivity
  · intro j hj
    have htj : 0 ≤ (j : ℝ) / t := by positivity
    have hrj : 0 ≤ (j : ℝ) / r := by positivity
    apply (div_le_one (by positivity : 0 < 1 + (j : ℝ) / r)).2
    linarith

/-- The exponential lower bound for the occupation ratio from the manuscript. -/
theorem exp_le_occupationRatio {t r : ℝ} {H : ℕ}
    (ht : 0 < t) (hr : 0 < r) (hH : (H : ℝ) ≤ t / 2) :
    Real.exp (-(H : ℝ) ^ 2 / t - (H : ℝ) ^ 2 / (2 * r)) ≤
      occupationRatio t r H := by
  have hfactor : ∀ j ∈ Finset.range H,
      Real.exp (-2 * ((j : ℝ) / t) - (j : ℝ) / r) ≤
        (1 - (j : ℝ) / t) / (1 + (j : ℝ) / r) := by
    intro j hj
    apply exp_le_occupation_factor (by positivity) _ (by positivity)
    apply (div_le_iff₀ ht).2
    have hjH : (j : ℝ) ≤ H := by exact_mod_cast (Finset.mem_range.mp hj).le
    linarith
  have hprod := Finset.prod_le_prod₀
    (fun j (_ : j ∈ Finset.range H) =>
      (Real.exp_pos (-2 * ((j : ℝ) / t) - (j : ℝ) / r)).le) hfactor
  rw [← Real.exp_sum] at hprod
  apply le_trans _ hprod
  apply Real.exp_le_exp.mpr
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.sum_div, ← Finset.sum_div]
  have hsum := sum_range_cast_le_half_sq H
  have hdivt := div_le_div_of_nonneg_right hsum ht.le
  have hdivr := div_le_div_of_nonneg_right hsum hr.le
  ring_nf at hdivt hdivr ⊢
  linarith

/-- A common loss bound applies uniformly to all factorial orders at most `H₀`. -/
theorem exp_le_occupationRatio_of_le {t r : ℝ} {H H₀ : ℕ}
    (ht : 0 < t) (hr : 0 < r) (hHH : H ≤ H₀) (hH₀ : (H₀ : ℝ) ≤ t / 2) :
    Real.exp (-(H₀ : ℝ) ^ 2 / t - (H₀ : ℝ) ^ 2 / (2 * r)) ≤
      occupationRatio t r H := by
  have hcast : (H : ℝ) ≤ H₀ := by exact_mod_cast hHH
  have hsq : (H : ℝ) ^ 2 ≤ (H₀ : ℝ) ^ 2 := by nlinarith [Nat.cast_nonneg (α := ℝ) H]
  apply le_trans _ (exp_le_occupationRatio ht hr (hcast.trans hH₀))
  apply Real.exp_le_exp.mpr
  have h₁ := div_le_div_of_nonneg_right hsq ht.le
  have h₂ := div_le_div_of_nonneg_right hsq (show 0 ≤ 2 * r by positivity)
  ring_nf at h₁ h₂ ⊢
  linarith

/-- In the lower-bound range the ratio is strictly positive. -/
theorem occupationRatio_pos {t r : ℝ} {H : ℕ}
    (ht : 0 < t) (hr : 0 < r) (hH : (H : ℝ) ≤ t / 2) :
    0 < occupationRatio t r H :=
  (Real.exp_pos _).trans_le (exp_le_occupationRatio ht hr hH)

end Problem335

end

end OAI
