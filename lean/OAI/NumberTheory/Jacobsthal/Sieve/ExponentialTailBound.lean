import Mathlib.Analysis.SpecialFunctions.Exponential
import OAI.NumberTheory.Jacobsthal.Estimates.LossBounds
import OAI.NumberTheory.Jacobsthal.Probability.OrderedAffineMoment

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

open _root_.Filter
open scoped Topology
namespace ErdosOmissionTail

noncomputable def expTerm (x : ℝ) (n : ℕ) : ℝ := x^n/(n.factorial:ℝ)
noncomputable def firstExpTerm (x : ℝ) (n : ℕ) : ℝ := (n:ℝ)*expTerm x n
noncomputable def secondExpTerm (x : ℝ) (n : ℕ) : ℝ := (n:ℝ)*((n:ℝ)-1)*expTerm x n
noncomputable def weightedExpTerm (x : ℝ) (n : ℕ) : ℝ := ((n:ℝ)+1)^2*expTerm x n

theorem expTerm_hasSum (x : ℝ) : HasSum (expTerm x) (Real.exp x) := by
  simpa only [Real.exp_eq_exp_ℝ] using! NormedSpace.expSeries_div_hasSum_exp x

theorem firstExpTerm_succ (x : ℝ) (n : ℕ) : firstExpTerm x (n+1)=x*expTerm x n := by
  unfold firstExpTerm expTerm
  rw [Nat.factorial_succ,pow_succ,Nat.cast_mul]
  have hn : ((n+1:ℕ):ℝ) ≠ 0 := by positivity
  field_simp

theorem secondExpTerm_add_two (x : ℝ) (n : ℕ) : secondExpTerm x (n+2)=x^2*expTerm x n := by
  unfold secondExpTerm expTerm
  rw [show n+2=(n+1)+1 by omega,Nat.factorial_succ,Nat.factorial_succ,pow_succ,pow_succ]
  push_cast
  have hn1 : (n:ℝ)+1 ≠ 0 := by positivity
  have hn2 : (n:ℝ)+1+1 ≠ 0 := by positivity
  field_simp
  ring

theorem firstExpTerm_hasSum (x : ℝ) : HasSum (firstExpTerm x) (x*Real.exp x) := by
  apply (hasSum_nat_add_iff' 1).mp
  have hh := (expTerm_hasSum x).mul_left x
  simp_rw [firstExpTerm_succ]
  simpa only [Finset.sum_range_one,firstExpTerm,Nat.cast_zero,zero_mul,sub_zero] using! hh

theorem secondExpTerm_hasSum (x : ℝ) : HasSum (secondExpTerm x) (x^2*Real.exp x) := by
  apply (hasSum_nat_add_iff' 2).mp
  have hh := (expTerm_hasSum x).mul_left (x^2)
  simp_rw [secondExpTerm_add_two]
  simpa only [Finset.sum_range_succ,Finset.sum_range_zero,Finset.sum_empty,
    secondExpTerm,Nat.cast_zero,Nat.cast_one,zero_mul,sub_self,mul_zero,add_zero,sub_zero] using! hh

theorem weightedExpTerm_hasSum (x : ℝ) :
    HasSum (weightedExpTerm x) ((x^2+3*x+1)*Real.exp x) := by
  have hh := ((secondExpTerm_hasSum x).add ((firstExpTerm_hasSum x).mul_left 3)).add (expTerm_hasSum x)
  convert! hh using 1
  · funext n
    unfold weightedExpTerm secondExpTerm firstExpTerm
    ring
  · ring

theorem weighted_log_two_tail_hasSum :
    HasSum (fun n : ℕ => weightedExpTerm (Real.log 2) (n+4))
      (1+2*Real.log 2-(5:ℝ)/2*(Real.log 2)^2-(8:ℝ)/3*(Real.log 2)^3) := by
  have hh := (hasSum_nat_add_iff' 4).mpr (weightedExpTerm_hasSum (Real.log 2))
  rw [Real.exp_log (by norm_num : (0:ℝ)<2)] at hh
  convert! hh using 1
  norm_num [weightedExpTerm,expTerm,Finset.sum_range_succ]
  ring

theorem weighted_log_two_tail_lt :
    (∑' n : ℕ,weightedExpTerm (Real.log 2) (n+4)) < (314:ℝ)/1000 := by
  rw [weighted_log_two_tail_hasSum.tsum_eq]
  have h := ErdosBoundaryLoss.log_two_bounds
  have hq : 0 < (Real.log 2)^2+(69:ℝ)/100*Real.log 2+(69:ℝ)^2/10000 := by positivity
  have hp := mul_pos (sub_pos.mpr h.1)
    (show 0 < (5:ℝ)/2*(Real.log 2+(69:ℝ)/100)+(8:ℝ)/3*
      ((Real.log 2)^2+(69:ℝ)/100*Real.log 2+(69:ℝ)^2/10000)-2 by nlinarith)
  nlinarith

theorem log_two_mean_factor_bounds :
    0 < 3/Real.log 2-2 ∧ 3/Real.log 2-2 < (235:ℝ)/100 := by
  have h := ErdosBoundaryLoss.log_two_bounds
  have hp : 0 < Real.log 2 := by linarith
  constructor
  · have hh : 2*Real.log 2 < 3 := by linarith
    exact sub_pos.mpr ((lt_div_iff₀ hp).mpr hh)
  · have hh : 3/Real.log 2 < (435:ℝ)/100 := (div_lt_iff₀ hp).mpr (by linarith)
    linarith

theorem numerical_tail_majorant_lt :
    (1:ℝ)/2*(3/Real.log 2-2)*(∑' n : ℕ,weightedExpTerm (Real.log 2) (n+4)) < (37:ℝ)/100 := by
  have hf := log_two_mean_factor_bounds
  have ht := weighted_log_two_tail_lt
  have hnon : 0 ≤ ∑' n : ℕ,weightedExpTerm (Real.log 2) (n+4) := by
    apply tsum_nonneg
    intro n
    unfold weightedExpTerm expTerm
    positivity
  have hm := mul_lt_mul_of_pos_left ht (mul_pos (by norm_num : (0:ℝ)<1/2) hf.1)
  have hf' := mul_lt_mul_of_pos_right hf.2 (by norm_num : (0:ℝ)<(314:ℝ)/2000)
  nlinarith

end ErdosOmissionTail

end

end Erdos970

end OAI
