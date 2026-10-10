import OAI.NumberTheory.TotientAsymptotic.SmallFactorMoment

namespace OAI

/-! Reciprocal mass of cofactors with too many small prime factors. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

lemma log_three_halves_lower : (1/3:ℝ) ≤ Real.log (3/2:ℝ) := by
  have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0:ℝ) < 3/2)
  norm_num at h ⊢
  exact h

lemma small_factor_tail_weight {S : ℝ} {n : ℕ} (hn : 0 < n)
    (hbad : 2*B S-1 < (omegaIn n 1 S:ℝ)) :
    (n:ℝ)⁻¹ ≤ Real.exp ((1-2*B S)*Real.log (3/2:ℝ))*intervalOmegaWeight (3/2) 1 S n := by
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  have hlog : 0 < Real.log (3/2:ℝ) := Real.log_pos (by norm_num)
  have he : 1 ≤ Real.exp ((1-2*B S)*Real.log (3/2:ℝ))*(3/2:ℝ)^(omegaIn n 1 S) := by
    rw [← Real.rpow_natCast,Real.rpow_def_of_pos (by norm_num : (0:ℝ) < 3/2),← Real.exp_add]
    apply Real.one_le_exp
    nlinarith
  have hh := mul_le_mul_of_nonneg_right he (inv_nonneg.mpr hnR.le)
  simpa only [intervalOmegaWeight,MonoidHom.coe_mk,OneHom.coe_mk,one_mul,div_eq_mul_inv,
    mul_assoc] using hh

 theorem small_factor_tail_mass : ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 2 ≤ N →
    ∀ S : ℝ, 2 ≤ S → 0 ≤ B S → ∀ Q : Finset ℕ,
    (∀ n ∈ Q,0 < n ∧ n ≤ N ∧ 2*B S-1 < (omegaIn n 1 S:ℝ)) →
    (∑ n ∈ Q,(n:ℝ)⁻¹) ≤ C*Real.log N*(Real.log S)^(-1/6:ℝ) := by
  obtain ⟨C,hC,hbound⟩ := small_factor_moment_bound
  refine ⟨(3/2:ℝ)*C,by positivity,?_⟩
  intro N hN S hS hBS Q hQ
  have hm := hbound N hN S hS Q (fun n hn => ⟨(hQ n hn).1,(hQ n hn).2.1⟩)
  have hlog : 0 < Real.log S := Real.log_pos (by linarith)
  have hNlog : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast (show 1 ≤ N by omega))
  have hexp : Real.exp ((1-2*B S)*Real.log (3/2:ℝ)+B S/2) ≤
      (3/2:ℝ)*(Real.log S)^(-1/6:ℝ) := by
    rw [Real.rpow_def_of_pos hlog,show (3/2:ℝ)=Real.exp (Real.log (3/2:ℝ)) from
      (Real.exp_log (by norm_num)).symm,← Real.exp_add]
    simp only [Real.log_exp]
    apply Real.exp_le_exp.mpr
    unfold B at *
    nlinarith [log_three_halves_lower]
  calc
    _ ≤ ∑ n ∈ Q,Real.exp ((1-2*B S)*Real.log (3/2:ℝ))*intervalOmegaWeight (3/2) 1 S n :=
      Finset.sum_le_sum (fun n hn => small_factor_tail_weight (hQ n hn).1 (hQ n hn).2.2)
    _ = Real.exp ((1-2*B S)*Real.log (3/2:ℝ))*(∑ n ∈ Q,intervalOmegaWeight (3/2) 1 S n) :=
      (Finset.mul_sum ..).symm
    _ ≤ Real.exp ((1-2*B S)*Real.log (3/2:ℝ))*(C*Real.log N*Real.exp (B S/2)) :=
      mul_le_mul_of_nonneg_left hm (Real.exp_pos _).le
    _ = C*Real.log N*Real.exp ((1-2*B S)*Real.log (3/2:ℝ)+B S/2) := by rw [Real.exp_add]; ring
    _ ≤ C*Real.log N*((3/2:ℝ)*(Real.log S)^(-1/6:ℝ)) :=
      mul_le_mul_of_nonneg_left hexp (mul_nonneg hC.le hNlog)
    _ = _ := by ring

end TotientAsymptotic

end

end OAI
