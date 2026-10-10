import OAI.NumberTheory.TotientAsymptotic.BootstrapNormalityDecay

namespace OAI

/-! Elementary log-log comparisons at dyadic endpoints. -/
noncomputable section
open scoped Topology
open Filter
namespace TotientAsymptotic

lemma dyadic_B_tendsto : Tendsto (fun J : ℕ => B ((2:ℝ)^J)) atTop atTop :=
  B_tendsto.comp (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1:ℝ)<2))

lemma double_log_double_le {x : ℝ} (hx : 2 ≤ x) : B (2*x) ≤ B x+1 := by
  have hx0 : 0 < x := by linarith
  have hl : 0 < Real.log x := Real.log_pos (by linarith)
  have hlog2 : Real.log (2:ℝ) ≤ Real.log x := Real.log_le_log (by norm_num) hx
  have hlog : Real.log (2*x) ≤ 2*Real.log x := by
    rw [Real.log_mul (by norm_num : (2:ℝ)≠0) hx0.ne']
    linarith
  have hp : 0 < Real.log (2*x) := Real.log_pos (by linarith)
  have hh := Real.log_le_log hp hlog
  rw [Real.log_mul (by norm_num : (2:ℝ)≠0) hl.ne'] at hh
  have htwo : Real.log (2:ℝ) ≤ 1 := by linarith [Real.log_two_lt_d9]
  change Real.log (Real.log (2*x)) ≤ Real.log (Real.log x)+1
  linarith

lemma dyadic_log_index_le {J : ℕ} (hJ : 1 ≤ J) :
    1+Real.log J ≤ B ((2:ℝ)^J)+2 := by
  have hlog2 : 0 < Real.log (2:ℝ) := Real.log_pos (by norm_num)
  have hJ0 : (0:ℝ) < J := by exact_mod_cast (show 0 < J by omega)
  rw [dyadic_endpoint_B,Real.log_mul hJ0.ne' hlog2.ne']
  have hh : Real.log (1/2:ℝ) ≤ Real.log (Real.log (2:ℝ)) :=
    Real.log_le_log (by norm_num) (by linarith [Real.log_two_gt_d9])
  norm_num only [Real.log_div,Real.log_one] at hh
  linarith [Real.log_two_lt_d9]

lemma dyadic_normality_polynomial {J : ℕ} (hJ : 1 ≤ J)
    (hb : 0 ≤ B ((2:ℝ)^J)) :
    (B (2*(2:ℝ)^J))^5*(1+Real.log J) ≤ (B ((2:ℝ)^J)+2)^6 := by
  have hx : (2:ℝ) ≤ 2^J := by
    have hh := pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) hJ
    simpa using hh
  have hB := double_log_double_le hx
  have hB0 : 0 ≤ B (2*(2:ℝ)^J) := by
    have hmono : B ((2:ℝ)^J) ≤ B (2*(2:ℝ)^J) :=
      Real.log_le_log (Real.log_pos (by linarith)) (Real.log_le_log (by positivity) (by nlinarith only [hx]))
    exact hb.trans hmono
  have hlog := dyadic_log_index_le hJ
  have hlog0 : 0 ≤ 1+Real.log J := by
    have hh := Real.log_nonneg (show (1:ℝ) ≤ J by exact_mod_cast hJ)
    linarith
  calc
    _ ≤ (B ((2:ℝ)^J)+2)^5*(B ((2:ℝ)^J)+2) :=
      mul_le_mul (pow_le_pow_left₀ hB0 (hB.trans (by linarith)) 5) hlog hlog0 (by positivity)
    _ = _ := by ring

end TotientAsymptotic

end

end OAI
