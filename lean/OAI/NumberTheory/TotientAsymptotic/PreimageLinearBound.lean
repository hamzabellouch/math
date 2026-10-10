import OAI.NumberTheory.TotientAsymptotic.TotientPreimageBound

namespace OAI

/-! A linear-times-log-log size bound for every preimage of a bounded totient. -/
noncomputable section
namespace TotientAsymptotic

theorem totient_preimage_linear_loglog : ∃ C : ℝ,0 < C ∧
    ∀ z : ℝ,Real.exp 2 ≤ z → ∀ n : ℕ,0 < n → (n.totient:ℝ) ≤ z →
      (n:ℝ) ≤ C*z*(B z+2) := by
  obtain ⟨C,hC,hratio⟩ := totient_ratio_loglog_bound
  refine ⟨C,hC,?_⟩
  intro z hz n hn hφ
  have hz0 : 0 < z := (Real.exp_pos 2).trans_le hz
  have hlz : 2 ≤ Real.log z := (Real.le_log_iff_exp_le hz0).mpr hz
  have hz1 : 1 ≤ z := (Real.one_le_exp (by norm_num : (0:ℝ)≤2)).trans hz
  have hzsq : z ≤ z^2 := by nlinarith only [hz1]
  have hsize : (n:ℝ) ≤ 2*z^2 := by
    have hq : (n:ℝ) ≤ 2*(n.totient:ℝ)^2 := by exact_mod_cast totient_preimage_quadratic hn
    have hφ0 : (0:ℝ) ≤ n.totient := Nat.cast_nonneg _
    exact hq.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hφ0 hφ 2) (by norm_num))
  have hN : Real.exp 2 ≤ 2*z^2 := hz.trans (by nlinarith only [hzsq,hz0])
  have hB : B (2*z^2) ≤ B z+2 := by
    have hlog2 : Real.log (2:ℝ) ≤ 1 := by
      have hh := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
      norm_num at hh ⊢
      exact hh
    have hlog3 : Real.log (3:ℝ) ≤ 2 := by
      have hh := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<3)
      norm_num at hh ⊢
      exact hh
    have hlog : Real.log (2*z^2) ≤ 3*Real.log z := by
      rw [Real.log_mul (by norm_num : (2:ℝ)≠0) (pow_ne_zero 2 hz0.ne'),Real.log_pow]
      norm_num only [Nat.cast_ofNat]
      nlinarith only [hlog2,hlz]
    have hlogpos : 0 < Real.log (2*z^2) := Real.log_pos (by nlinarith only [hz1])
    have hh := Real.log_le_log hlogpos hlog
    rw [Real.log_mul (by norm_num : (3:ℝ)≠0) (by linarith only [hlz] : Real.log z≠0)] at hh
    change Real.log (Real.log (2*z^2)) ≤ Real.log (Real.log z)+2
    linarith only [hh,hlog3]
  have hratio' := hratio (2*z^2) hN n hn hsize
  have hφpos : (0:ℝ) < n.totient := by exact_mod_cast Nat.totient_pos.mpr hn
  have hmain := (div_le_iff₀ hφpos).mp hratio'
  have hBpos : 0 ≤ B (2*z^2) := Real.log_nonneg
    (by have hh := (Real.le_log_iff_exp_le (show 0<2*z^2 by positivity)).mpr hN; linarith only [hh])
  calc
    (n:ℝ) ≤ C*B (2*z^2)*(n.totient:ℝ) := hmain
    _ ≤ C*B (2*z^2)*z := mul_le_mul_of_nonneg_left hφ (mul_nonneg hC.le hBpos)
    _ ≤ C*z*(B z+2) := by
      have hh := mul_le_mul_of_nonneg_left hB (mul_nonneg hC.le hz0.le)
      nlinarith only [hh]

end TotientAsymptotic

end

end OAI
