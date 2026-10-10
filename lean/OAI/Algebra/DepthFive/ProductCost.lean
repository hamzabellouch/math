import Mathlib

namespace OAI

/-!
# Numerical assembly of the product-rank estimates

These lemmas isolate the finite-product and real-power calculations in the
all-low and one-high cases of the circuit rank estimate.  All hypotheses on
individual factor costs and parameters remain explicit.
-/

open scoped BigOperators

namespace Problem335

/-- Assemble individual exponential errors and favorable powers of a base at
most one.  This applies regardless of the source of the factor estimates. -/
theorem prod_cost_le_exp_mul_rpow {ι : Type*} (s : Finset ι)
    (H err d : ι → ℝ) (q E D : ℝ) (hq : 0 < q) (hq1 : q ≤ 1)
    (hH : ∀ j ∈ s, 0 ≤ H j)
    (hcost : ∀ j ∈ s, H j ≤ Real.exp (err j) * q ^ d j)
    (herr : (∑ j ∈ s, err j) ≤ E) (hd : D ≤ ∑ j ∈ s, d j) :
    (∏ j ∈ s, H j) ≤ Real.exp E * q ^ D := by
  calc
    (∏ j ∈ s, H j) ≤ ∏ j ∈ s, Real.exp (err j) * q ^ d j :=
      Finset.prod_le_prod₀ hH hcost
    _ = Real.exp (∑ j ∈ s, err j) * q ^ (∑ j ∈ s, d j) := by
      rw [Finset.prod_mul_distrib, ← Real.exp_sum, ← Real.rpow_sum_of_pos hq]
    _ ≤ Real.exp E * q ^ D :=
      mul_le_mul (Real.exp_le_exp.mpr herr)
        (Real.rpow_le_rpow_of_exponent_ge hq hq1 hd)
        (Real.rpow_nonneg (le_of_lt hq) _) (le_of_lt (Real.exp_pos E))

/-- The favorable power in the all-low case saves the exact manuscript
exponent `sqrt(n)/20`. -/
theorem all_low_power_saving (n q s : ℝ) (hn : 1 ≤ n) (hq : 0 ≤ q)
    (hqbound : q ≤ n ^ (-(2 : ℝ) / 5)) (hs : Real.sqrt n / 2 ≤ s) :
    q ^ (s / 4) ≤ n ^ (-Real.sqrt n / 20) := by
  have hs0 : 0 ≤ s := le_trans (by positivity) hs
  calc
    q ^ (s / 4) ≤ (n ^ (-(2 : ℝ) / 5)) ^ (s / 4) :=
      Real.rpow_le_rpow hq hqbound (by positivity)
    _ = n ^ (-s / 10) := by
      rw [← Real.rpow_mul (by linarith : 0 ≤ n)]
      congr 1
      ring
    _ ≤ n ^ (-Real.sqrt n / 20) :=
      Real.rpow_le_rpow_of_exponent_le hn (by linarith)

/-- The favorable power from expanding one high-degree factor saves the exact
manuscript exponent `3*sqrt(n)/160`. -/
theorem one_high_power_saving (n q lam t : ℝ) (hn : 1 ≤ n) (hq : 0 ≤ q)
    (hqbound : q ≤ n ^ (-(2 : ℝ) / 5)) (hlam : (3 : ℝ) / 8 ≤ lam)
    (ht : Real.sqrt n / 4 ≤ t) :
    q ^ (lam * t / 2) ≤ n ^ (-(3 * Real.sqrt n) / 160) := by
  have hlam0 : 0 ≤ lam := by linarith
  have ht0 : 0 ≤ t := le_trans (by positivity) ht
  have hlt : (3 / 8 : ℝ) * (Real.sqrt n / 4) ≤ lam * t :=
    mul_le_mul hlam ht (by positivity) hlam0
  calc
    q ^ (lam * t / 2) ≤ (n ^ (-(2 : ℝ) / 5)) ^ (lam * t / 2) :=
      Real.rpow_le_rpow hq hqbound (by positivity)
    _ = n ^ (-(lam * t) / 5) := by
      rw [← Real.rpow_mul (by linarith : 0 ≤ n)]
      congr 1
      ring
    _ ≤ n ^ (-(3 * Real.sqrt n) / 160) :=
      Real.rpow_le_rpow_of_exponent_le hn (by nlinarith)

/-- The bounded loss per remaining large factor is exponential in `sqrt n`. -/
theorem high_factor_exponential_bound (n s : ℝ) (hs : s ≤ Real.sqrt n) :
    (5 : ℝ) ^ (4 * s) ≤ Real.exp (4 * Real.log 5 * Real.sqrt n) := by
  rw [Real.rpow_def_of_pos (by norm_num)]
  apply Real.exp_le_exp.mpr
  have hlog : 0 ≤ Real.log 5 := Real.log_nonneg (by norm_num)
  nlinarith

/-- The number of large positive-degree factor occurrences is charged to their
total degree, rather than to the number of distinct circuit gates. -/
theorem large_degree_count_mul_le_sum {ι : Type*} (s : Finset ι)
    (e : ι → ℝ) (t : ℝ) (he : ∀ j ∈ s, 0 ≤ e j) :
    ((s.filter (fun j => t ≤ e j)).card : ℝ) * t ≤ ∑ j ∈ s, e j := by
  classical
  calc
    ((s.filter (fun j => t ≤ e j)).card : ℝ) * t =
        ∑ j ∈ s.filter (fun j => t ≤ e j), t := by simp
    _ ≤ ∑ j ∈ s.filter (fun j => t ≤ e j), e j := by
      apply Finset.sum_le_sum
      intro j hj
      exact (Finset.mem_filter.mp hj).2
    _ ≤ ∑ j ∈ s, e j :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun j hj _ => he j hj)

/-- Division form of the large-degree occurrence count. -/
theorem large_degree_count_le {ι : Type*} (s : Finset ι)
    (e : ι → ℝ) (t : ℝ) (ht : 0 < t) (he : ∀ j ∈ s, 0 ≤ e j) :
    ((s.filter (fun j => t ≤ e j)).card : ℝ) ≤ (∑ j ∈ s, e j) / t := by
  exact (le_div_iff₀ ht).mpr (large_degree_count_mul_le_sum s e t he)

/-- The all-low branch fits the common circuit-rank envelope.  No sign
assumption on the error constant `C` is required. -/
theorem all_low_common_rank_bound (n S D C : ℝ) (hn : 1 ≤ n)
    (hS : 1 ≤ S) (hD : 0 ≤ D) :
    2 * D * Real.exp (4 * C * Real.sqrt n) * n ^ (-Real.sqrt n / 20) ≤
      2 * S * D * Real.exp ((4 * C + 4 * Real.log 5) * Real.sqrt n) *
        n ^ (-Real.sqrt n / 100) := by
  have hc : 2 * D ≤ 2 * S * D := by nlinarith
  have he : Real.exp (4 * C * Real.sqrt n) ≤
      Real.exp ((4 * C + 4 * Real.log 5) * Real.sqrt n) := by
    apply Real.exp_le_exp.mpr
    have hh : 0 ≤ Real.log 5 * Real.sqrt n :=
      mul_nonneg (Real.log_nonneg (by norm_num)) (Real.sqrt_nonneg _)
    nlinarith
  have hp : n ^ (-Real.sqrt n / 20) ≤ n ^ (-Real.sqrt n / 100) :=
    Real.rpow_le_rpow_of_exponent_le hn (by nlinarith [Real.sqrt_nonneg n])
  exact mul_le_mul
    (mul_le_mul hc he (le_of_lt (Real.exp_pos _)) (by positivity)) hp
    (Real.rpow_nonneg (by linarith) _) (by positivity)

/-- The one-high branch fits the same envelope, absorbing the bounded cost of
all remaining high-degree factors. -/
theorem one_high_common_rank_bound (n s S D C : ℝ) (hn : 1 ≤ n)
    (hs : s ≤ Real.sqrt n) (hS : 0 ≤ S) (hD : 0 ≤ D) :
    2 * S * D * (5 : ℝ) ^ (4 * s) * Real.exp (4 * C * Real.sqrt n) *
        n ^ (-(3 * Real.sqrt n) / 160) ≤
      2 * S * D * Real.exp ((4 * C + 4 * Real.log 5) * Real.sqrt n) *
        n ^ (-Real.sqrt n / 100) := by
  have he : (5 : ℝ) ^ (4 * s) * Real.exp (4 * C * Real.sqrt n) ≤
      Real.exp ((4 * C + 4 * Real.log 5) * Real.sqrt n) := by
    calc
      _ ≤ Real.exp (4 * Real.log 5 * Real.sqrt n) *
          Real.exp (4 * C * Real.sqrt n) :=
        mul_le_mul_of_nonneg_right (high_factor_exponential_bound n s hs)
          (le_of_lt (Real.exp_pos _))
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have hp : n ^ (-(3 * Real.sqrt n) / 160) ≤ n ^ (-Real.sqrt n / 100) :=
    Real.rpow_le_rpow_of_exponent_le hn (by nlinarith [Real.sqrt_nonneg n])
  calc
    _ = (2 * S * D) * ((5 : ℝ) ^ (4 * s) * Real.exp (4 * C * Real.sqrt n)) *
        n ^ (-(3 * Real.sqrt n) / 160) := by ring
    _ ≤ _ := mul_le_mul (mul_le_mul_of_nonneg_left he (by positivity)) hp
      (Real.rpow_nonneg (by linarith) _) (by positivity)

/-- Summing at most `S` upper-product contributions gives the quadratic gate
factor in the circuit-rank proposition. -/
theorem sum_branch_rank_bound {ι : Type*} (s : Finset ι) (R : ι → ℝ)
    (n S D C : ℝ) (hn : 0 ≤ n) (hS : 0 ≤ S) (hD : 0 ≤ D)
    (hcard : (s.card : ℝ) ≤ S)
    (hR : ∀ j ∈ s, R j ≤
      2 * S * D * Real.exp (C * Real.sqrt n) * n ^ (-Real.sqrt n / 100)) :
    (∑ j ∈ s, R j) ≤
      2 * S ^ 2 * D * Real.exp (C * Real.sqrt n) * n ^ (-Real.sqrt n / 100) := by
  calc
    _ ≤ ∑ _j ∈ s,
        2 * S * D * Real.exp (C * Real.sqrt n) * n ^ (-Real.sqrt n / 100) :=
      Finset.sum_le_sum hR
    _ = (s.card : ℝ) *
        (2 * S * D * Real.exp (C * Real.sqrt n) * n ^ (-Real.sqrt n / 100)) := by
      simp
    _ ≤ S * (2 * S * D * Real.exp (C * Real.sqrt n) * n ^ (-Real.sqrt n / 100)) :=
      mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = _ := by ring

/-- Splitting large and small degrees multiplies their two distinct types of
cost, with the large-factor multiplicity retained exactly. -/
theorem prod_high_low_cost_le {ι : Type*} (s : Finset ι)
    (H err e : ι → ℝ) (t B E : ℝ)
    (hH : ∀ j ∈ s, 0 ≤ H j) (hB : 0 ≤ B)
    (hhigh : ∀ j ∈ s, t ≤ e j → H j ≤ B)
    (hlow : ∀ j ∈ s, e j < t → H j ≤ Real.exp (err j))
    (herr : (∑ j ∈ s with e j < t, err j) ≤ E) :
    (∏ j ∈ s, H j) ≤
      B ^ (s.filter (fun j => t ≤ e j)).card * Real.exp E := by
  classical
  calc
    _ ≤ ∏ j ∈ s, if t ≤ e j then B else Real.exp (err j) := by
      apply Finset.prod_le_prod₀ hH
      intro j hj
      split_ifs with h
      · exact hhigh j hj h
      · exact hlow j hj (lt_of_not_ge h)
    _ = B ^ (s.filter (fun j => t ≤ e j)).card *
        Real.exp (∑ j ∈ s with e j < t, err j) := by
      rw [Finset.prod_ite]
      simp only [Finset.prod_const, not_le, ← Real.exp_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr herr)
      (pow_nonneg hB _)

/-- A degree budget replaces the number of high factors by `N/t`. -/
theorem prod_high_low_cost_le_rpow {ι : Type*} (s : Finset ι)
    (H err e : ι → ℝ) (t B E N : ℝ) (ht : 0 < t)
    (hH : ∀ j ∈ s, 0 ≤ H j) (hB : 1 ≤ B)
    (he : ∀ j ∈ s, 0 ≤ e j) (hbudget : (∑ j ∈ s, e j) ≤ N)
    (hhigh : ∀ j ∈ s, t ≤ e j → H j ≤ B)
    (hlow : ∀ j ∈ s, e j < t → H j ≤ Real.exp (err j))
    (herr : (∑ j ∈ s with e j < t, err j) ≤ E) :
    (∏ j ∈ s, H j) ≤ B ^ (N / t) * Real.exp E := by
  have hcount : ((s.filter (fun j => t ≤ e j)).card : ℝ) ≤ N / t :=
    (large_degree_count_le s e t ht he).trans
      ((div_le_div_iff_of_pos_right ht).mpr hbudget)
  calc
    _ ≤ B ^ (s.filter (fun j => t ≤ e j)).card * Real.exp E :=
      prod_high_low_cost_le s H err e t B E hH (by linarith) hhigh hlow herr
    _ = B ^ ((s.filter (fun j => t ≤ e j)).card : ℝ) * Real.exp E := by
      rw [Real.rpow_natCast]
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow_of_exponent_le hB hcount) (le_of_lt (Real.exp_pos _))

/-- Expanding one factor of degree at least `t` supplies enough linear-factor
cost to obtain the favorable power `q^(lam*t/2)`. -/
theorem linear_factor_cost_power_le (H q lam t : ℝ) (e : ℕ)
    (hH : 0 ≤ H) (hq : 0 < q) (hq1 : q ≤ 1) (hlam : 0 ≤ lam)
    (hcost : H ≤ q ^ (lam / 2)) (he : t ≤ (e : ℝ)) :
    H ^ e ≤ q ^ (lam * t / 2) := by
  calc
    H ^ e ≤ (q ^ (lam / 2)) ^ e := pow_le_pow_left₀ hH hcost e
    _ = q ^ (lam * (e : ℝ) / 2) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (le_of_lt hq)]
      congr 1
      ring
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_ge hq hq1
      (by nlinarith [mul_le_mul_of_nonneg_left he hlam])

/-- The abstract one-high expansion estimate, before inserting the analytic
parameter bounds.  The finite family represents the unexpanded occurrences. -/
theorem expanded_high_product_cost_le {ι : Type*} (s : Finset ι)
    (H err e : ι → ℝ) (Hlin q lam t B E N : ℝ) (d : ℕ)
    (ht : 0 < t) (hH : ∀ j ∈ s, 0 ≤ H j) (hB : 1 ≤ B)
    (he : ∀ j ∈ s, 0 ≤ e j) (hbudget : (∑ j ∈ s, e j) ≤ N)
    (hhigh : ∀ j ∈ s, t ≤ e j → H j ≤ B)
    (hlow : ∀ j ∈ s, e j < t → H j ≤ Real.exp (err j))
    (herr : (∑ j ∈ s with e j < t, err j) ≤ E)
    (hHlin : 0 ≤ Hlin) (hq : 0 < q) (hq1 : q ≤ 1) (hlam : 0 ≤ lam)
    (hlinear : Hlin ≤ q ^ (lam / 2)) (hd : t ≤ (d : ℝ)) :
    Hlin ^ d * (∏ j ∈ s, H j) ≤
      B ^ (N / t) * Real.exp E * q ^ (lam * t / 2) := by
  calc
    _ ≤ q ^ (lam * t / 2) * (B ^ (N / t) * Real.exp E) :=
      mul_le_mul (linear_factor_cost_power_le Hlin q lam t d hHlin hq hq1 hlam hlinear hd)
        (prod_high_low_cost_le_rpow s H err e t B E N ht hH hB he hbudget hhigh hlow herr)
        (Finset.prod_nonneg hH) (Real.rpow_nonneg (le_of_lt hq) _)
    _ = _ := by ring

end Problem335

end OAI
