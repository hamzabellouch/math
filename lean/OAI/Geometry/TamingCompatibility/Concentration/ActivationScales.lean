import Mathlib
import OAI.Geometry.TamingCompatibility.Charts.SlowLogCutoff

namespace OAI

section

noncomputable section
open Filter MeasureTheory
open scoped Topology ENNReal
namespace TamingCompatibility.SummableCutoff

def stepSize (n : ℕ) : ℝ := (1/2)^n
lemma stepSize_pos (n : ℕ) : 0 < stepSize n := pow_pos (by norm_num) _
lemma stepSize_le_one (n : ℕ) : stepSize n ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
lemma summable_stepSize : Summable stepSize := summable_geometric_of_abs_lt_one (by norm_num)
lemma tendsto_stepSize : Tendsto stepSize atTop (𝓝 0) := summable_stepSize.tendsto_atTop_zero

def thresholdScale (n : ℕ) : ℝ := stepSize n * Real.exp (-(1/stepSize n))
lemma thresholdScale_pos (n : ℕ) : 0 < thresholdScale n := mul_pos (stepSize_pos n) (Real.exp_pos _)
lemma logActivation_step_threshold (n : ℕ) {t : ℝ} (h : stepSize n ≤ t) :
    1 ≤ logActivation (stepSize n) (thresholdScale n) t := by
  exact logActivation_threshold (stepSize_pos n) (thresholdScale_pos n)
    (threshold_scale_pos (stepSize_pos n) (stepSize_pos n)).2 h

lemma exists_activation_scales (f g h : ℝ → ℝ)
    (hf : Tendsto f (𝓝[>] 0) (𝓝 0)) (hg : Tendsto g (𝓝[>] 0) (𝓝 0))
    (hh : Tendsto h (𝓝[>] 0) (𝓝 0)) :
    ∃ r : ℕ → ℝ, (∀ n, 0 < r n ∧ r n ≤ 1) ∧ Tendsto r atTop (𝓝 0) ∧
      ∀ n, f (r n) ≤ thresholdScale n ∧ g (r n) ≤ thresholdScale n ∧ h (r n) ≤ thresholdScale n := by
  have he (n : ℕ) : ∃ r : ℝ, 0 < r ∧ r ≤ stepSize n ∧
      f r ≤ thresholdScale n ∧ g r ≤ thresholdScale n ∧ h r ≤ thresholdScale n := by
    have hr : ∀ᶠ r in 𝓝[>] (0:ℝ), r < stepSize n :=
      nhdsWithin_le_nhds (gt_mem_nhds (stepSize_pos n))
    obtain ⟨r,hrpos,hrn,hfr,hgr,hhr⟩ :=
      ((show ∀ᶠ r in 𝓝[>] (0:ℝ), 0 < r from self_mem_nhdsWithin).and (hr.and
        ((hf.eventually (gt_mem_nhds (thresholdScale_pos n))).and
          ((hg.eventually (gt_mem_nhds (thresholdScale_pos n))).and
            (hh.eventually (gt_mem_nhds (thresholdScale_pos n))))))).exists
    exact ⟨r,hrpos,hrn.le,hfr.le,hgr.le,hhr.le⟩
  choose r hr hsmall hbound using he
  refine ⟨r,fun n => ⟨hr n,(hsmall n).trans (stepSize_le_one n)⟩,?_,hbound⟩
  exact squeeze_zero (fun n => (hr n).le) hsmall tendsto_stepSize

lemma logActivation_integral_bound {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (f : X → ℝ) (ε δ : ℝ) (hε : 0 ≤ ε) (hδ : 0 < δ) (hf : ∀ x, 0 ≤ f x)
    (hi : Integrable f μ) (hc : Integrable (fun x => logActivation ε δ (f x)) μ) :
    (∫ x, logActivation ε δ (f x) ∂μ) ≤ (ε/δ)*(∫ x, f x ∂μ) := by
  rw [← integral_const_mul]
  exact integral_mono hc (hi.const_mul _) (fun x => logActivation_le hε hδ (hf x))

lemma weighted_nonneg_ratio_bound {ε δ t e : ℝ} (hε : 0 ≤ ε) (hδ : 0 < δ)
    (ht : 0 ≤ t) (he : 0 ≤ e) :
    (ε/(δ+t))*(t+e) ≤ ε+(ε/δ)*e := by
  have hd : 0 < δ+t := by positivity
  have ht' : (ε/(δ+t))*t ≤ ε := by
    rw [div_mul_eq_mul_div,div_le_iff₀ hd]
    nlinarith
  have he' : (ε/(δ+t))*e ≤ (ε/δ)*e :=
    mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_left hε hδ (by linarith)) he
  nlinarith
end TamingCompatibility.SummableCutoff

end
end

end OAI
