import OAI.NumberTheory.TotientAsymptotic.BootstrapResidualSize
import OAI.NumberTheory.TotientAsymptotic.FordCofactorStep

namespace OAI

/-! A large surviving value has a largest prime in the quarter-power range. -/
noncomputable section
open scoped Topology
open Filter
namespace TotientAsymptotic

lemma bootstrap_residual_quarter : ∀ᶠ x : ℝ in atTop,
    Real.exp ((Real.log x)^(81/100:ℝ)) ≤ x^(1/4:ℝ) := by
  have ht := (tendsto_rpow_neg_atTop (by norm_num : (0:ℝ)<19/100)).comp Real.tendsto_log_atTop
  filter_upwards [ht.eventually (eventually_lt_nhds (by norm_num : (0:ℝ)<1/4)),
    eventually_gt_atTop (1:ℝ)] with x hx hx1
  have hl : 0 < Real.log x := Real.log_pos hx1
  have hp : (Real.log x)^(81/100:ℝ)=(Real.log x)*(Real.log x)^(-(19/100:ℝ)) := by
    calc
      _ = (Real.log x)^((1:ℝ)+(-(19/100:ℝ))) := by norm_num
      _ = (Real.log x)^(1:ℝ)*(Real.log x)^(-(19/100:ℝ)) := Real.rpow_add hl _ _
      _ = _ := by rw [Real.rpow_one]
  change (Real.log x)^(-(19/100:ℝ)) < 1/4 at hx
  rw [Real.rpow_def_of_pos (by linarith : 0<x)]
  apply Real.exp_le_exp.mpr
  rw [hp]
  exact mul_le_mul_of_nonneg_left hx.le hl.le

lemma quarter_prime_of_residual {x : ℝ} {n : ℕ} (hx : 1 < x) (hn : 0 < n)
    (htail : (fordCofactor n 2:ℝ) ≤ x^(1/4:ℝ))
    (hv : x^(3/4:ℝ) < (n.totient:ℝ)) :
    x^(1/4:ℝ) ≤ fordPrime n 0 := by
  have hx0 : 0 < x := by linarith
  have hpow : 0 < x^(1/4:ℝ) := Real.rpow_pos_of_pos hx0 _
  have horder : (fordPrime n 1:ℝ) ≤ fordPrime n 0 := by exact_mod_cast fordPrime_le_first n 1
  have h0 : 0 ≤ (fordPrime n 0:ℝ) := Nat.cast_nonneg _
  have htail0 : 0 ≤ (fordCofactor n 2:ℝ) := Nat.cast_nonneg _
  have hbound : (n:ℝ) ≤ (fordPrime n 0:ℝ)^2*(fordCofactor n 2:ℝ) := by
    have he := congrArg (fun m : ℕ => (m:ℝ)) (ford_first_two_factorization hn)
    simp only [Nat.cast_mul] at he
    nlinarith only [he,mul_le_mul_of_nonneg_left horder h0,htail0]
  by_contra hh
  have hp : (fordPrime n 0:ℝ) < x^(1/4:ℝ) := lt_of_not_ge hh
  have hs : (fordPrime n 0:ℝ)^2 < (x^(1/4:ℝ))^2 := by nlinarith
  have hprod : (n:ℝ) < (x^(1/4:ℝ))^2*x^(1/4:ℝ) :=
    hbound.trans_lt ((mul_le_mul_of_nonneg_left htail (sq_nonneg _)).trans_lt
      (mul_lt_mul_of_pos_right hs hpow))
  have hid : (x^(1/4:ℝ))^2*x^(1/4:ℝ)=x^(3/4:ℝ) := by
    rw [pow_two,← Real.rpow_add hx0,← Real.rpow_add hx0]
    norm_num
  rw [hid] at hprod
  have hφ : (n.totient:ℝ) ≤ n := Nat.cast_le.mpr (Nat.totient_le n)
  linarith

lemma quarter_fordPrime_prime {x : ℝ} {n : ℕ} (hx : 1 < x)
    (hp : x^(1/4:ℝ) ≤ fordPrime n 0) : (fordPrime n 0).Prime := by
  have hlarge : 1 < (fordPrime n 0:ℝ) := (Real.one_lt_rpow hx (by norm_num)).trans_le hp
  by_cases hi : 0 < n.primeFactorsList.length
  · exact fordPrime_prime hi
  · have he : fordPrime n 0=1 := by
      unfold fordPrime
      rw [List.getElem?_eq_none (by simp only [List.length_reverse]; omega)]
      rfl
    simp only [he,Nat.cast_one,lt_self_iff_false] at hlarge

end TotientAsymptotic

end

end OAI
