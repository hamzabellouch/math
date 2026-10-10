import OAI.NumberTheory.TotientAsymptotic.RenewalMagnitude

namespace OAI

/-! A small root separation for the sign of Ford's transformed coefficients. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

lemma renewalSeries_three_sevenths_lt_one : renewalSeries (3/7)<1 := by
  let r : ℝ := 3/7
  have hr0 : 0≤r := by norm_num [r]
  have hr1 : r<1 := by norm_num [r]
  have hs := summable_renewal hr0 hr1
  have hg := hasSum_choose_mul_geometric_of_norm_lt_one (𝕜 := ℝ) 1
    (r := r) (by norm_num [r])
  have hsg : HasSum (fun n : ℕ => ((n+1 : ℕ) : ℝ)*r^(n+1)) (21/16 : ℝ) := by
    convert hg.mul_right r using 1
    · ext n
      simp only [Nat.choose_one_right,Nat.cast_add,Nat.cast_one,pow_succ]
      ring
    · norm_num [r]
  have htail : (∑' n : ℕ, a (n+2+1)*r^(n+2+1)) ≤
      ∑' n : ℕ, ((n+2+1 : ℕ) : ℝ)*r^(n+2+1) := by
    apply ((summable_nat_add_iff 2).mpr hs).tsum_le_tsum
    · intro n
      exact mul_le_mul_of_nonneg_right
        (by exact_mod_cast a_le_index (j := n+2+1) (by omega)) (pow_nonneg hr0 _)
    · exact (summable_nat_add_iff 2).mpr hsg.summable
  have hf := hs.sum_add_tsum_nat_add 2
  have hi := hsg.summable.sum_add_tsum_nat_add 2
  rw [hsg.tsum_eq] at hi
  change _=renewalSeries r at hf
  norm_num [Finset.sum_range_succ,r] at hf hi htail
  have ha1 : a 1<1/2 := by
    norm_num [a]
    linarith [Real.log_two_lt_d9]
  have ha2 : a 2<1 := by
    norm_num [a]
    linarith [Real.log_two_gt_d9,Real.log_three_lt_d9]
  change renewalSeries r<1
  nlinarith

lemma rho_gt_three_sevenths : (3/7 : ℝ)<rho := by
  by_contra! hh
  have hm := renewalSeries_strictMonoOn.monotoneOn
    (show rho∈Set.Ico (0 : ℝ) 1 from ⟨rho_pos.le,rho_lt_one⟩)
    (show (3/7 : ℝ)∈Set.Ico (0 : ℝ) 1 by norm_num) hh
  rw [renewalSeries_rho] at hm
  linarith [renewalSeries_three_sevenths_lt_one]

lemma renewal_first_transformed_negative : rho⁻¹-a 1-2<0 := by
  have hr : rho⁻¹<(7/3 : ℝ) := by
    rw [inv_eq_one_div]
    apply (div_lt_iff₀ rho_pos).mpr
    nlinarith [rho_gt_three_sevenths]
  have ha : (1/3 : ℝ)<a 1 := by
    norm_num [a]
    linarith [Real.log_two_gt_d9]
  linarith

end TotientAsymptotic

end

end OAI
