import OAI.NumberTheory.TotientAsymptotic.QuarterPowerBudget

namespace OAI

/-! The size of the explicit residual cutoff for Ford's exponential row slack. -/
noncomputable section
namespace TotientAsymptotic

def rowModelDecay (t : ℝ) : ℝ :=
  (Real.exp (-t/40)/40000)^2/(12000000*(t+2)^6)

def rowModelConstant (F : ℝ) : ℝ := Real.log 2000000000+
  (4/3:ℝ)*(Real.log (10000*(F+31)^2)+2*Real.log 40000+Real.log 12000000)+
  8*(Real.log 24000+1)

lemma row_model_decay_bounds {t : ℝ} (ht : 0 ≤ t) :
    0 < rowModelDecay t ∧ rowModelDecay t ≤ 1 := by
  have he : Real.exp (-t/40) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hp : 1 ≤ (t+2)^6 := one_le_pow₀ (by linarith)
  constructor
  · unfold rowModelDecay
    positivity
  · unfold rowModelDecay
    apply (div_le_iff₀ (by positivity : 0 < 12000000*(t+2)^6)).mpr
    have hx : 0 ≤ Real.exp (-t/40)/40000 := by positivity
    have hx1 : Real.exp (-t/40)/40000 ≤ 1 := by linarith
    nlinarith only [hx,hx1,hp]

lemma row_model_decay_log {t : ℝ} (ht : 0 ≤ t) :
    Real.log (rowModelDecay t) =
      -t/20-2*Real.log 40000-Real.log 12000000-6*Real.log (t+2) := by
  unfold rowModelDecay
  rw [Real.log_div (by positivity) (by positivity),Real.log_pow,
    Real.log_div (Real.exp_ne_zero _) (by norm_num),Real.log_exp,
    Real.log_mul (by norm_num) (by positivity),Real.log_pow]
  ring

lemma row_model_constant_nonneg {F : ℝ} (hF : 0 ≤ F) : 0 ≤ rowModelConstant F := by
  have hK : 1 ≤ 10000*(F+31)^2 := by nlinarith only [hF,sq_nonneg F]
  have h0 := Real.log_nonneg hK
  have h1 := Real.log_nonneg (by norm_num : (1:ℝ)≤2000000000)
  have h2 := Real.log_nonneg (by norm_num : (1:ℝ)≤40000)
  have h3 := Real.log_nonneg (by norm_num : (1:ℝ)≤12000000)
  have h4 := Real.log_nonneg (by norm_num : (1:ℝ)≤24000)
  unfold rowModelConstant
  positivity

lemma row_model_cutoff_log_bound {F t : ℝ} (hF : 0 ≤ F) (ht : 0 ≤ t) :
    0 ≤ Real.log (rowMassCutoffHeight F (rowModelDecay t)+4) ∧
    Real.log (rowMassCutoffHeight F (rowModelDecay t)+4) ≤
      (67/1000:ℝ)*t+rowModelConstant F := by
  have hd := row_model_decay_bounds ht
  have hbound := row_mass_cutoff_log_bound hF hd.1 hd.2
  rw [row_model_decay_log ht] at hbound
  have hlog : Real.log (t+2) ≤ t/24000+Real.log 24000+1 := by
    have hh := Real.log_le_sub_one_of_pos (by positivity : 0 < (t+2)/24000)
    rw [Real.log_div (by linarith : t+2≠0) (by norm_num)] at hh
    linarith only [hh]
  have hb0 : 0 ≤ rowMassCutoffHeight F (rowModelDecay t) := by
    unfold rowMassCutoffHeight
    exact mul_nonneg (by norm_num) (Real.rpow_nonneg (div_nonneg (by positivity) hd.1.le) _)
  refine ⟨Real.log_nonneg (by linarith only [hb0]),?_⟩
  unfold rowModelConstant
  linarith only [hbound,hlog]

lemma row_model_mass_exponent_bound {F t : ℝ} (hF : 0 ≤ F) (ht : 0 ≤ t) :
    10*(Real.log (rowMassCutoffHeight F (rowModelDecay t)+4))^2 ≤
      t^2/21+210*(rowModelConstant F)^2 := by
  obtain ⟨hL,hbound⟩ := row_model_cutoff_log_bound hF ht
  have hC := row_model_constant_nonneg hF
  have hsq : (Real.log (rowMassCutoffHeight F (rowModelDecay t)+4))^2 ≤
      ((67/1000:ℝ)*t+rowModelConstant F)^2 := by nlinarith only [hL,hbound,hC,ht]
  have hy := sq_nonneg ((67/1000:ℝ)*t-20*rowModelConstant F)
  nlinarith only [hsq,hy,sq_nonneg t]

end TotientAsymptotic

end

end OAI
