import OAI.NumberTheory.TotientAsymptotic.HeavyOmegaMoment
import OAI.NumberTheory.TotientAsymptotic.FullOmegaTail
import OAI.NumberTheory.TotientAsymptotic.NormalitySmallParameter

namespace OAI

/-! The excessive-prime-factor exception at the five-log-log threshold. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

lemma log_fifteen_eighths_lower : (5/8:ℝ) ≤ Real.log (15/8:ℝ) := by
  have hh := Real.sum_range_le_log_div (x:=7/23) (by norm_num) (by norm_num) 2
  norm_num [Finset.sum_range_succ] at hh
  linarith

lemma heavy_factor_tail_weight {b : ℝ} {n : ℕ} (hn : 0 < n)
    (hbad : 5*b ≤ (n.primeFactorsList.length:ℝ)) :
    (n:ℝ)⁻¹ ≤ Real.exp (-5*b*Real.log (15/8:ℝ))*heavyOmegaReciprocal n := by
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  have hlog : 0 < Real.log (15/8:ℝ) := Real.log_pos (by norm_num)
  have he : 1 ≤ Real.exp (-5*b*Real.log (15/8:ℝ))*(15/8:ℝ)^n.primeFactorsList.length := by
    rw [← Real.rpow_natCast,Real.rpow_def_of_pos (by norm_num : (0:ℝ) < 15/8),← Real.exp_add]
    apply Real.one_le_exp
    nlinarith only [mul_le_mul_of_nonneg_right hbad hlog.le]
  have hh := mul_le_mul_of_nonneg_right he (inv_nonneg.mpr hnR.le)
  simpa only [heavyOmegaReciprocal,MonoidHom.coe_mk,OneHom.coe_mk,one_mul,div_eq_mul_inv,
    mul_assoc] using hh

/-- In particular, the excessive-Omega exception is smaller than
`N / log(N)^(1+1/6)`, the largest saving required for the nice-value count. -/
theorem heavy_factor_tail_count : ∃ C : ℝ,0 < C ∧ ∀ N : ℕ,4 ≤ N →
    ∀ Q : Finset ℕ,(∀ n ∈ Q,0 < n ∧ n ≤ N ∧ 5*B N ≤ (n.primeFactorsList.length:ℝ)) →
    (Q.card:ℝ) ≤ C*N*(Real.log N)^(-5/4:ℝ) := by
  obtain ⟨C,hC,hmoment⟩ := heavy_omega_moment_bound
  refine ⟨C,hC,?_⟩
  intro N hN Q hQ
  have hlog : 0 < Real.log N := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hB : 0 ≤ B N := (doubleLog_nat_pos hN).le
  have hm := hmoment N (by omega) Q (fun n hn => ⟨(hQ n hn).1,(hQ n hn).2.1⟩)
  have hrec : (∑ n ∈ Q,(n:ℝ)⁻¹) ≤
      Real.exp (-5*B N*Real.log (15/8:ℝ))*(∑ n ∈ Q,heavyOmegaReciprocal n) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun n hn => heavy_factor_tail_weight (hQ n hn).1 (hQ n hn).2.2)
  have he : Real.exp (-5*B N*Real.log (15/8:ℝ))*(Real.log N)^(15/8:ℝ) ≤
      (Real.log N)^(-5/4:ℝ) := by
    rw [Real.rpow_def_of_pos hlog,Real.rpow_def_of_pos hlog,← Real.exp_add]
    apply Real.exp_le_exp.mpr
    change -5*B N*Real.log (15/8:ℝ)+B N*(15/8:ℝ) ≤ B N*(-5/4:ℝ)
    nlinarith only [mul_le_mul_of_nonneg_right log_fifteen_eighths_lower hB]
  have hc := card_le_endpoint_reciprocal Q N (fun n hn =>
    ⟨(hQ n hn).1,by exact_mod_cast (hQ n hn).2.1⟩)
  calc
    _ ≤ N*(Real.exp (-5*B N*Real.log (15/8:ℝ))*(C*(Real.log N)^(15/8:ℝ))) :=
      hc.trans (mul_le_mul_of_nonneg_left (hrec.trans
        (mul_le_mul_of_nonneg_left hm (Real.exp_pos _).le)) (Nat.cast_nonneg N))
    _ = C*N*(Real.exp (-5*B N*Real.log (15/8:ℝ))*(Real.log N)^(15/8:ℝ)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left he (by positivity)

end TotientAsymptotic

end

end OAI
