import OAI.NumberTheory.TotientAsymptotic.ThirdPrimeSize
import OAI.NumberTheory.TotientAsymptotic.PreimageOmega

namespace OAI

/-! After two leading primes, a surviving preimage has a subpower residual. -/
noncomputable section
open scoped Topology
open Filter
namespace TotientAsymptotic

lemma fordCofactor_le_power (n k : ℕ) :
    fordCofactor n k ≤ (fordPrime n k)^n.primeFactorsList.length := by
  by_cases hk : k < n.primeFactorsList.length
  · let l := n.primeFactorsList.reverse.drop k
    have hmem (p : ℕ) (hp : p ∈ l) : p ≤ fordPrime n k := by
      obtain ⟨i,hi,he⟩ := List.mem_iff_getElem.mp hp
      have hki : k+i < n.primeFactorsList.length := by
        dsimp [l] at hi
        simp only [List.length_drop,List.length_reverse] at hi
        omega
      have he' : fordPrime n (k+i)=p := by
        rw [fordPrime_eq_get hki]
        simpa only [l,List.getElem_drop] using he
      rw [← he']
      exact fordPrime_antitone hk hki (by omega)
    have hp1 : 1 ≤ fordPrime n k := (fordPrime_prime hk).one_le
    have hl : l.length ≤ n.primeFactorsList.length := by simp [l]
    exact (List.prod_le_pow_length l _ hmem).trans (pow_le_pow_right₀ hp1 hl)
  · have hl : n.primeFactorsList.length ≤ k := by omega
    have hp : fordPrime n k=1 := by
      unfold fordPrime
      rw [List.getElem?_eq_none (by simpa using hl)]
      rfl
    have hd : n.primeFactorsList.reverse.drop k = [] :=
      List.drop_eq_nil_iff.mpr (by simpa using hl)
    simp only [fordCofactor,hd,List.prod_nil,hp,one_pow,le_refl]

lemma fordCofactor_log_le (n k : ℕ) :
    Real.log (fordCofactor n k) ≤ n.primeFactorsList.length*Real.log (fordPrime n k) := by
  have hp := fordCofactor_pos n k
  have hh := Real.log_le_log (by exact_mod_cast hp) (Nat.cast_le.mpr (fordCofactor_le_power n k))
  simpa only [Nat.cast_pow,Real.log_pow] using hh

lemma bootstrap_factor_scale : ∀ᶠ x : ℝ in atTop,
    5*B x+1 ≤ (Real.log x)^(1/100:ℝ) := by
  have h1 : Tendsto (fun b : ℝ => b*Real.exp (-(1/100:ℝ)*b)) atTop (nhds 0) := by
    simpa only [Real.rpow_one] using
      (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (1:ℝ) (1/100) (by norm_num))
  have h0 : Tendsto (fun b : ℝ => Real.exp (-(1/100:ℝ)*b)) atTop (nhds 0) := by
    simpa only [Real.rpow_zero,one_mul] using
      (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (0:ℝ) (1/100) (by norm_num))
  have ht := ((h1.const_mul 5).add h0).comp B_tendsto
  simp only [mul_zero,add_zero] at ht
  filter_upwards [ht.eventually (eventually_lt_nhds (by norm_num : (0:ℝ)<1)),
    eventually_gt_atTop (1:ℝ)] with x hx hx1
  have hlog : 0 < Real.log x := Real.log_pos hx1
  change 5*(B x*Real.exp (-(1/100:ℝ)*B x))+Real.exp (-(1/100:ℝ)*B x) < 1 at hx
  have he : (5*B x+1)*Real.exp (-(1/100:ℝ)*B x) ≤ 1 := by nlinarith only [hx]
  have hh := mul_le_mul_of_nonneg_right he (Real.exp_pos ((1/100:ℝ)*B x)).le
  have hid : Real.exp (-(1/100:ℝ)*B x)*Real.exp ((1/100:ℝ)*B x)=1 := by
    rw [← Real.exp_add]
    simp
  rw [mul_assoc,hid,mul_one,one_mul] at hh
  simpa only [Real.rpow_def_of_pos hlog,B,mul_comm] using hh

theorem bootstrap_cofactor_size : ∀ᶠ x : ℝ in atTop,∀ n : ℕ,0 < n →
    (n.totient.primeFactorsList.length:ℝ) ≤ 5*B x →
    a 1*fordPrimeCoordinate n 1+a 2*fordPrimeCoordinate n 2 ≤ (101/100:ℝ)*B x →
    (fordCofactor n 2:ℝ) ≤ Real.exp ((Real.log x)^(81/100:ℝ)) := by
  filter_upwards [bootstrap_factor_scale,eventually_gt_atTop (1:ℝ)] with x hx hx1
  intro n hn hΩ hscore
  have hlog : 0 < Real.log x := Real.log_pos hx1
  have hlen : (n.primeFactorsList.length:ℝ) ≤ 5*B x+1 := by
    have hh : (n.primeFactorsList.length:ℝ) ≤ n.totient.primeFactorsList.length+1 := by
      exact_mod_cast preimage_factor_count hn
    linarith
  have hprime := third_prime_size hx1 hscore
  have hprimeLog : Real.log (fordPrime n 2) ≤ (Real.log x)^(4/5:ℝ) := by
    have hp : 0 < fordPrime n 2 := by
      by_cases hi : 2 < n.primeFactorsList.length
      · exact (fordPrime_prime hi).pos
      · unfold fordPrime
        rw [List.getElem?_eq_none (by simpa using Nat.le_of_not_gt hi)]
        norm_num
    have hh := Real.log_le_log (by exact_mod_cast hp) hprime
    simpa only [Real.log_exp] using hh
  have hcof : Real.log (fordCofactor n 2) ≤ (Real.log x)^(81/100:ℝ) := by
    calc
      _ ≤ n.primeFactorsList.length*Real.log (fordPrime n 2) := fordCofactor_log_le n 2
      _ ≤ (5*B x+1)*(Real.log x)^(4/5:ℝ) :=
        (mul_le_mul_of_nonneg_left hprimeLog (Nat.cast_nonneg _)).trans
          (mul_le_mul_of_nonneg_right hlen (Real.rpow_nonneg hlog.le _))
      _ ≤ (Real.log x)^(1/100:ℝ)*(Real.log x)^(4/5:ℝ) :=
        mul_le_mul_of_nonneg_right hx (Real.rpow_nonneg hlog.le _)
      _ = _ := by rw [← Real.rpow_add hlog]; norm_num
  exact (Real.log_le_iff_le_exp (by exact_mod_cast fordCofactor_pos n 2)).mp hcof

theorem bootstrap_residual_size : ∀ᶠ x : ℝ in atTop,∀ n : ℕ,0 < n →
    (n.totient.primeFactorsList.length:ℝ) ≤ 5*B x →
    a 1*fordPrimeCoordinate n 1+a 2*fordPrimeCoordinate n 2 ≤ (101/100:ℝ)*B x →
    ((fordCofactor n 2).totient:ℝ) ≤ Real.exp ((Real.log x)^(81/100:ℝ)) := by
  filter_upwards [bootstrap_cofactor_size] with x hx
  intro n hn hΩ hscore
  exact (Nat.cast_le.mpr (Nat.totient_le (fordCofactor n 2))).trans (hx n hn hΩ hscore)

end TotientAsymptotic

end

end OAI
