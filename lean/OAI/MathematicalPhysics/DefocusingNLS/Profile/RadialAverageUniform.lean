import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialInnerDerivative
import Mathlib.Topology.MetricSpace.UniformConvergence

namespace OAI

/-! Uniform continuity of the regular radial derivative integral, including the origin. -/

open Set Filter MeasureTheory
namespace DefocusingNLS

theorem radialAverage_sub_on (R r : ℝ) (hr : r ∈ Icc 0 R) (f g : ℝ → ℝ)
    (hf : ContinuousOn f (Icc 0 R)) (hg : ContinuousOn g (Icc 0 R)) :
    radialAverage (fun t => f t-g t) r=radialAverage f r-radialAverage g r := by
  have hm : MapsTo (fun s => r*s) (Icc (0 : ℝ) 1) (Icc 0 R) := by
    intro s hs
    exact ⟨mul_nonneg hr.1 hs.1,(mul_le_of_le_one_right hr.1 hs.2).trans hr.2⟩
  have hfc : ContinuousOn (fun s => f (r*s)*s^11) (Icc (0 : ℝ) 1) :=
    (hf.comp (continuous_const.mul continuous_id).continuousOn hm).mul
      (continuous_id.pow 11).continuousOn
  have hgc : ContinuousOn (fun s => g (r*s)*s^11) (Icc (0 : ℝ) 1) :=
    (hg.comp (continuous_const.mul continuous_id).continuousOn hm).mul
      (continuous_id.pow 11).continuousOn
  unfold radialAverage
  rw [← intervalIntegral.integral_sub
    (ContinuousOn.intervalIntegrable_of_Icc (by norm_num) hfc)
    (ContinuousOn.intervalIntegrable_of_Icc (by norm_num) hgc)]
  apply intervalIntegral.integral_congr
  intro s _
  ring

theorem radial_derivative_integral_uniform (R : ℝ) (hR : 0 ≤ R)
    (f : ℕ → ℝ → ℝ) (g : ℝ → ℝ)
    (hf : ∀ i, ContinuousOn (f i) (Icc 0 R)) (hg : ContinuousOn g (Icc 0 R))
    (ht : TendstoUniformlyOn f g atTop (Icc 0 R)) :
    TendstoUniformlyOn (fun i r => r*radialAverage (f i) r)
      (fun r => r*radialAverage g r) atTop (Icc 0 R) := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  let δ := ε/(R+1)
  have hδ : 0 < δ := div_pos hε (by linarith)
  have hδε : δ*(R+1)=ε := div_mul_cancel₀ _ (by linarith)
  filter_upwards [(Metric.tendstoUniformlyOn_iff.mp ht) δ hδ] with i hi r hr
  have ha := radialAverage_norm_le (fun t => f i t-g t) R δ r hr.1 hr.2 (by
    intro t ht
    have hh := (hi t ht).le
    simpa only [dist_comm,dist_eq_norm] using hh)
  rw [radialAverage_sub_on R r hr (f i) g (hf i) hg] at ha
  rw [dist_comm,dist_eq_norm,← mul_sub,norm_mul,Real.norm_eq_abs,abs_of_nonneg hr.1]
  have hh := mul_le_mul_of_nonneg_left ha hr.1
  have hrδ := mul_le_mul_of_nonneg_right hr.2 (show 0 ≤ δ/12 by positivity)
  nlinarith

end DefocusingNLS

end OAI
