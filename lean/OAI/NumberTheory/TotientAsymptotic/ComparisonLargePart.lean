import OAI.NumberTheory.TotientAsymptotic.ComparisonSizes
import OAI.NumberTheory.TotientAsymptotic.BandComparison

namespace OAI

/-! The largest-prime restriction supplies Ford's required part above `Y₁`. -/

noncomputable section
open scoped Topology
open Filter

namespace TotientAsymptotic

lemma comparison_small_part_cost : ∀ᶠ y : ℝ in atTop,
    (4*B y)*Real.exp ((4/5 : ℝ)*B y) ≤ (1/10 : ℝ)*Real.log y := by
  have ht : Tendsto (fun b : ℝ => 4*b*Real.exp (-(1/5 : ℝ)*b)) atTop (nhds 0) := by
    simpa only [Real.rpow_one,mul_assoc,mul_zero] using
      (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 (1/5) (by norm_num)).const_mul 4
  filter_upwards [(ht.comp B_tendsto).eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1/10)),
    eventually_gt_atTop (1 : ℝ)] with y hy hy1
  have he : Real.exp (B y)=Real.log y := Real.exp_log (Real.log_pos hy1)
  have hh := mul_le_mul_of_nonneg_right hy.le (Real.exp_pos (B y)).le
  change (4*B y*Real.exp (-(1/5 : ℝ)*B y))*Real.exp (B y) ≤
    (1/10 : ℝ)*Real.exp (B y) at hh
  have heq : (4*B y*Real.exp (-(1/5 : ℝ)*B y))*Real.exp (B y) =
      (4*B y)*Real.exp ((4/5 : ℝ)*B y) := by
    rw [mul_assoc,← Real.exp_add]
    congr 2
    ring
  rwa [heq,he] at hh

lemma prime_shift_log_lower : ∀ᶠ y : ℝ in atTop, ∀ p : ℕ, p.Prime →
    y^(9/10 : ℝ) ≤ p → (4/5 : ℝ)*Real.log y ≤ Real.log (p-1 : ℕ) := by
  filter_upwards [eventually_gt_atTop (1 : ℝ),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (10*Real.log 2))] with y hy hlog
  intro p hp hlo
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hp' : (p : ℝ)-1=(p-1 : ℕ) := by rw [Nat.cast_sub hp.one_lt.le]; norm_num
  have hhalf : y^(9/10 : ℝ)/2 ≤ (p-1 : ℕ) := by
    rw [← hp']
    linarith
  have hh := Real.log_le_log (div_pos (Real.rpow_pos_of_pos (zero_lt_one.trans hy) _) (by norm_num)) hhalf
  rw [Real.log_div (Real.rpow_pos_of_pos (zero_lt_one.trans hy) _).ne' (by norm_num : (2 : ℝ) ≠ 0),
    Real.log_rpow (zero_lt_one.trans hy)] at hh
  linarith

/-- The large prime part of the first shift exceeds `sqrt y`. The hypotheses
are exactly the size consequences supplied by normality and the ordered grid. -/
theorem comparison_large_prime_part : ∀ᶠ y : ℝ in atTop, ∀ p : ℕ, ∀ Z : ℝ,
    p.Prime → y^(9/10 : ℝ) ≤ p → 1 ≤ Z →
    Z ≤ Real.exp (Real.exp ((4/5 : ℝ)*B y)) →
    ((p-1).primeFactorsList.length : ℝ) ≤ 4*B y →
    Real.sqrt y < (partAbove (p-1) Z : ℝ) := by
  filter_upwards [comparison_small_part_cost,prime_shift_log_lower,
    eventually_gt_atTop (1 : ℝ),B_tendsto.eventually (eventually_gt_atTop (0 : ℝ))]
    with y hcost hshift hy hB
  intro p Z hp hlo hZ hZu hΩ
  apply partAbove_gt_sqrt (Nat.sub_pos_of_lt hp.one_lt) hZ hΩ (zero_lt_one.trans hy)
  have hlZ := Real.log_le_log (lt_of_lt_of_le zero_lt_one hZ) hZu
  rw [Real.log_exp] at hlZ
  have hprod := mul_le_mul_of_nonneg_left hlZ (show 0 ≤ 4*B y by positivity)
  have hh := hshift p hp hlo
  linarith [Real.log_pos hy]

end TotientAsymptotic

end

end OAI
