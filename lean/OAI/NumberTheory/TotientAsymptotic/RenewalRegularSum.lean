import OAI.NumberTheory.TotientAsymptotic.RenewalMoment
import OAI.NumberTheory.TotientAsymptotic.RenewalSeriesAlgebra

namespace OAI

/-! The constant term at the renewal pole, using absolutely convergent sums. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

lemma summable_norm_regular_weighted :
    Summable (fun n : ℕ => ‖renewalRegular n*rho^n‖) := by
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _
    ((summable_geometric_of_lt_one rho_pos.le rho_lt_one).mul_left 4)
  intro n
  rw [norm_mul,Real.norm_eq_abs (rho^n),abs_of_pos (pow_pos rho_pos n),Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right (renewalRegular_bound n) (pow_pos rho_pos n).le

lemma regular_weighted_sum_eq_gamma :
    (∑' n : ℕ, renewalRegular n*rho^n)=gamma := by
  have hL : Summable (fun n : ℕ => ‖renewalTail n*rho^n‖) := by
    convert renewalTail_weighted_sum.1 using 1
    ext n
    exact Real.norm_of_nonneg (mul_nonneg (renewalTail_nonneg n) (pow_pos rho_pos n).le)
  have ht := tsum_mul_tsum_eq_tsum_sum_range_of_summable_norm hL summable_norm_regular_weighted
  have he (n : ℕ) : (∑ j ∈ Finset.range (n+1),
      (renewalTail j*rho^j)*(renewalRegular (n-j)*rho^(n-j)))=
      if n=0 then 1 else 0 := by
    calc
      _ = (∑ j ∈ Finset.range (n+1), renewalTail j*renewalRegular (n-j))*rho^n := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro j hj
        have hjn : j≤n := by have := Finset.mem_range.mp hj; omega
        have hp : rho^j*rho^(n-j)=rho^n := by rw [← pow_add,Nat.add_sub_of_le hjn]
        calc
          _ = (renewalTail j*renewalRegular (n-j))*(rho^j*rho^(n-j)) := by ring
          _ = _ := by rw [hp]
      _ = _ := by rw [renewalTail_regular_convolution]; split_ifs with hn <;> simp [hn]
  simp only [he] at ht
  rw [renewalTail_weighted_sum.2] at ht
  have hs : (∑' n : ℕ, if n=0 then (1 : ℝ) else 0)=1 := by simp
  rw [hs] at ht
  have hmul := congrArg (fun x : ℝ => gamma*x) ht
  simpa only [← mul_assoc,mul_inv_cancel₀ gamma_pos.ne',one_mul,mul_one] using hmul

lemma normalized_renewal_eq_regular_partial (n : ℕ) :
    g n*rho^n=∑ j ∈ Finset.range (n+1), renewalRegular j*rho^j := by
  induction n with
  | zero => simp [g,renewalRegular_zero]
  | succ n ih =>
    rw [Finset.sum_range_succ,← ih,renewalRegular_recurrence,pow_succ]
    field_simp [rho_pos.ne']
    ring

end TotientAsymptotic

end

end OAI
