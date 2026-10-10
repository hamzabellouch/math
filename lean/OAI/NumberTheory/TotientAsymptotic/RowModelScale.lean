import OAI.NumberTheory.TotientAsymptotic.RowCutoffModel

namespace OAI

/-! The row cutoff and decay rate fit below the ambient Ford scale. -/
noncomputable section
open scoped Topology
open Filter
namespace TotientAsymptotic

lemma row_model_height_eventually {F : ℝ} (hF : 0 ≤ F) :
    ∀ᶠ t : ℝ in atTop,
      rowMassCutoffHeight F (rowModelDecay t)+4 ≤ Real.exp (t/2) := by
  filter_upwards [eventually_ge_atTop (0:ℝ),
    eventually_ge_atTop (100*(rowModelConstant F+1))] with t ht hlarge
  obtain ⟨_,hlog⟩ := row_model_cutoff_log_bound hF ht
  have hb : 0 < rowMassCutoffHeight F (rowModelDecay t)+4 := by
    unfold rowMassCutoffHeight
    have hd := (row_model_decay_bounds ht).1
    positivity
  have he := Real.exp_le_exp.mpr (show Real.log (rowMassCutoffHeight F (rowModelDecay t)+4) ≤ t/2 by
    linarith only [hlog,hlarge,ht])
  simpa only [Real.exp_log hb] using he

lemma row_model_decay_eventually : ∀ᶠ t : ℝ in atTop,
    Real.exp (-t/2) ≤ rowModelDecay t := by
  let D : ℝ := 2*Real.log 40000+Real.log 12000000+6*(Real.log 24000+1)
  filter_upwards [eventually_ge_atTop (0:ℝ),eventually_ge_atTop (100*(D+1))]
    with t ht hlarge
  have hlog : Real.log (t+2) ≤ t/24000+Real.log 24000+1 := by
    have hh := Real.log_le_sub_one_of_pos (by positivity : 0 < (t+2)/24000)
    rw [Real.log_div (by linarith : t+2≠0) (by norm_num)] at hh
    linarith only [hh]
  have he : -t/2 ≤ Real.log (rowModelDecay t) := by
    rw [row_model_decay_log ht]
    dsimp [D] at hlarge
    linarith only [hlog,hlarge,ht]
  simpa only [Real.exp_log (row_model_decay_bounds ht).1] using Real.exp_le_exp.mpr he

lemma row_model_quadratic_eventually : ∀ᶠ t : ℝ in atTop,
    t^2/4 ≤ Real.exp (t/10) := by
  have hh := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (2:ℝ) (1/10:ℝ) (by norm_num)).eventually
    (eventually_lt_nhds (by norm_num : (0:ℝ)<4))
  filter_upwards [hh] with t ht
  have hpow : t^(2:ℝ)=t^2 := Real.rpow_natCast t 2
  have hdiv : t^2/Real.exp (t/10) ≤ 4 := by
    change t^(2:ℝ)*Real.exp (-(1/10:ℝ)*t)<4 at ht
    rw [hpow,show -(1/10:ℝ)*t=-(t/10) by ring,Real.exp_neg] at ht
    simpa only [div_eq_mul_inv] using ht.le
  have hb := (div_le_iff₀ (Real.exp_pos (t/10))).mp hdiv
  linarith only [hb]

lemma row_model_ambient_budget {F : ℝ} (hF : 0 ≤ F) :
    ∀ᶠ t : ℝ in atTop, ∀ b : ℝ,Real.exp ((3/5:ℝ)*t) ≤ b →
      rowMassCutoffHeight F (rowModelDecay t)+4 ≤ b ∧
      t^2/4 ≤ rowModelDecay t*b := by
  filter_upwards [row_model_height_eventually hF,row_model_decay_eventually,
    row_model_quadratic_eventually,eventually_ge_atTop (0:ℝ)] with t hh hd hq ht
  intro b hb
  refine ⟨hh.trans ((Real.exp_le_exp.mpr (by linarith)).trans hb),?_⟩
  have hm := mul_le_mul hd hb (Real.exp_pos _).le (row_model_decay_bounds ht).1.le
  have he : Real.exp (-t/2)*Real.exp ((3/5:ℝ)*t)=Real.exp (t/10) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [he] at hm
  exact hq.trans hm

end TotientAsymptotic

end

end OAI
