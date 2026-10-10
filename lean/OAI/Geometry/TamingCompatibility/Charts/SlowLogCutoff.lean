import Mathlib

namespace OAI

section

noncomputable section
open Filter
open scoped Topology
namespace TamingCompatibility.SummableCutoff

def logActivation (ε δ t : ℝ) : ℝ := ε * Real.log (1+t/δ)

lemma logActivation_nonneg {ε δ t : ℝ} (hε : 0 ≤ ε) (hδ : 0 < δ) (ht : 0 ≤ t) :
    0 ≤ logActivation ε δ t := by
  apply mul_nonneg hε
  apply Real.log_nonneg
  have : 0 ≤ t/δ := div_nonneg ht hδ.le
  linarith

lemma logActivation_le {ε δ t : ℝ} (hε : 0 ≤ ε) (hδ : 0 < δ) (ht : 0 ≤ t) :
    logActivation ε δ t ≤ (ε/δ)*t := by
  calc
    _ ≤ ε*((1+t/δ)-1) := mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos (by positivity)) hε
    _ = _ := by ring

lemma hasDerivAt_logActivation {ε δ t : ℝ} (hδ : 0 < δ) (ht : 0 ≤ t) :
    HasDerivAt (logActivation ε δ) (ε/(δ+t)) t := by
  have hp : 0 < 1+t/δ := by positivity
  have hh := (((hasDerivAt_id t).div_const δ).const_add 1).log hp.ne'
  have he : ε * (1 / δ / (1 + t / δ)) = ε / (δ+t) := by
    field_simp
  convert! hh.const_mul ε using 1
  simpa only [id_eq] using he.symm

lemma logActivation_deriv_bound {ε δ t : ℝ} (hε : 0 ≤ ε) (hδ : 0 < δ) (ht : 0 ≤ t) :
    |deriv (logActivation ε δ) t| ≤ ε/δ ∧
      t*|deriv (logActivation ε δ) t| ≤ ε := by
  rw [(hasDerivAt_logActivation hδ ht).deriv,abs_of_nonneg (div_nonneg hε (by positivity))]
  have hd : 0 < δ+t := by positivity
  constructor
  · exact div_le_div_of_nonneg_left hε hδ (by linarith)
  · rw [← mul_div_assoc,div_le_iff₀ hd]
    nlinarith

lemma logActivation_threshold {ε δ a t : ℝ} (hε : 0 < ε) (hδ : 0 < δ)
    (ha : δ*Real.exp (1/ε) ≤ a) (ht : a ≤ t) : 1 ≤ logActivation ε δ t := by
  have hx : Real.exp (1/ε) ≤ 1+t/δ := by
    have hh := (le_div_iff₀ hδ).2 (show Real.exp (1/ε)*δ ≤ t by simpa only [mul_comm] using ha.trans ht)
    linarith
  have hlog := Real.log_le_log (Real.exp_pos (1/ε)) hx
  rw [Real.log_exp] at hlog
  have hm := mul_le_mul_of_nonneg_left hlog hε.le
  have he : ε*(1/ε) = 1 := by field_simp
  exact he ▸ hm

lemma threshold_scale_pos {ε a : ℝ} (_hε : 0 < ε) (ha : 0 < a) :
    0 < a*Real.exp (-(1/ε)) ∧
      (a*Real.exp (-(1/ε)))*Real.exp (1/ε) ≤ a := by
  refine ⟨mul_pos ha (Real.exp_pos _),?_⟩
  rw [mul_assoc,←Real.exp_add,neg_add_cancel,Real.exp_zero,mul_one]

lemma tendsto_of_summable_activation {c f a : ℕ → ℝ}
    (hc : Summable c) (hf : ∀ n, 0 ≤ f n)
    (ha : Tendsto a atTop (𝓝 0))
    (hthreshold : ∀ n, a n ≤ f n → 1 ≤ c n) :
    Tendsto f atTop (𝓝 0) := by
  have he : ∀ᶠ n in atTop, f n ≤ a n := by
    filter_upwards [hc.tendsto_atTop_zero.eventually (gt_mem_nhds (by norm_num : (0:ℝ) < 1))] with n hn
    exact le_of_lt (lt_of_not_ge (fun h => (not_le_of_gt hn) (hthreshold n h)))
  exact squeeze_zero' (Eventually.of_forall hf) he ha

end TamingCompatibility.SummableCutoff

end
end

end OAI
