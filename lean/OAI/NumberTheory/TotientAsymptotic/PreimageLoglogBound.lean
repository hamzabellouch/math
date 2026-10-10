import OAI.NumberTheory.TotientAsymptotic.TotientPreimageBound

namespace OAI

/-! A uniform range for every preimage of every totient up to x. -/
noncomputable section
namespace TotientAsymptotic

lemma doubleLog_twice_square {x : ℝ} (hx : Real.exp (Real.exp 1) ≤ x) :
    B (2*x^2) ≤ 3*B x := by
  have hexp : 2 ≤ Real.exp (1:ℝ) := by linarith [Real.add_one_le_exp (1:ℝ)]
  have hx2 : Real.exp 2 ≤ x := (Real.exp_le_exp.mpr hexp).trans hx
  have hx0 : 0 < x := (Real.exp_pos 2).trans_le hx2
  have hl : 2 ≤ Real.log x := (Real.le_log_iff_exp_le hx0).mpr hx2
  have hB : 1 ≤ B x := by
    have hh := Real.log_le_log (Real.exp_pos (1:ℝ))
      ((Real.le_log_iff_exp_le hx0).mpr hx)
    simpa only [Real.log_exp,B] using hh
  have he : Real.log (2*x^2)=Real.log 2+2*Real.log x := by
    rw [Real.log_mul (by norm_num) (pow_ne_zero _ hx0.ne'),Real.log_pow]
    norm_num
  have hh : Real.log (2*x^2) ≤ 3*Real.log x := by
    rw [he]
    linarith [Real.log_two_lt_d9]
  have hlpos : 0 < Real.log (2*x^2) := by rw [he]; positivity
  have hlog := Real.log_le_log hlpos hh
  rw [Real.log_mul (by norm_num) (by linarith : Real.log x ≠ 0)] at hlog
  have h3 : Real.log (3:ℝ) ≤ 2 := by simpa only [show (3:ℝ)-1=2 by norm_num] using Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<3)
  change B (2*x^2) ≤ Real.log 3+B x at hlog
  linarith

theorem preimage_loglog_bound : ∃ C : ℝ,0 < C ∧
    ∀ x : ℝ,Real.exp (Real.exp 1) ≤ x → ∀ n : ℕ,0 < n → (n.totient:ℝ) ≤ x →
      (n:ℝ) ≤ C*x*B x := by
  obtain ⟨C,hC,hratio⟩ := totient_ratio_loglog_bound
  refine ⟨3*C,by positivity,?_⟩
  intro x hx n hn hφ
  have hx0 : 0 < x := (Real.exp_pos _).trans_le hx
  have hx1 : 1 < x := (Real.one_lt_exp_iff.mpr (Real.exp_pos _)).trans_le hx
  have hφ0 : (0:ℝ) < n.totient := by exact_mod_cast Nat.totient_pos.mpr hn
  have hnX : (n:ℝ) ≤ 2*x^2 := by
    have hh : (n:ℝ) ≤ 2*(n.totient:ℝ)^2 := by exact_mod_cast totient_preimage_quadratic hn
    exact hh.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hφ0.le hφ 2) (by norm_num))
  have hX : Real.exp 2 ≤ 2*x^2 := by
    have he : 2 ≤ Real.exp (1:ℝ) := by linarith [Real.add_one_le_exp (1:ℝ)]
    have hy : Real.exp 2 ≤ x := (Real.exp_le_exp.mpr he).trans hx
    nlinarith
  have hh := (hratio (2*x^2) hX n hn hnX).trans
    (mul_le_mul_of_nonneg_left (doubleLog_twice_square hx) hC.le)
  have hnonneg : 0 ≤ C*(3*B x) := (div_pos (by exact_mod_cast hn) hφ0).le.trans hh
  calc
    (n:ℝ) = ((n:ℝ)/n.totient)*n.totient := (div_mul_cancel₀ _ hφ0.ne').symm
    _ ≤ (C*(3*B x))*n.totient := mul_le_mul_of_nonneg_right hh hφ0.le
    _ ≤ (C*(3*B x))*x := mul_le_mul_of_nonneg_left hφ hnonneg
    _ = _ := by ring

end TotientAsymptotic

end

end OAI
