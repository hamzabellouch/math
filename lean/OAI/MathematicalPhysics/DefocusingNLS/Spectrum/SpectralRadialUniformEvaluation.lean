import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralRadialRepresentative
import Mathlib.Topology.UniformSpace.UniformApproximation

namespace OAI

/-! Uniform evaluation on positive annuli and continuity of the H¹ representative. -/

open Set MeasureTheory Filter Topology
open scoped SchwartzMap
namespace DefocusingNLS

theorem spectralRadialPointValue_annulus_bound (R δ : ℝ) (hR : 0 < R) (hδ : 0 < δ)
    (r : ℝ) (hr : r ∈ Icc δ R) (u : SpectralRadialEnergy R) :
    ‖spectralRadialPointValue R hR r (hδ.trans_le hr.1) u‖ ≤
      (1+spectralRadialEvaluationWeight R hR δ)*‖u‖ := by
  have hb := spectralRadialPointValue_sq_bound R hR r (hδ.trans_le hr.1) hr.2 u
  have hw : spectralRadialEvaluationWeight R hR r ≤ spectralRadialEvaluationWeight R hR δ := by
    unfold spectralRadialEvaluationWeight
    have hi := inv_anti₀ (pow_pos hδ 10) (pow_le_pow_left₀ hδ.le hr.1 10)
    linarith
  have hδw : 0 ≤ spectralRadialEvaluationWeight R hR δ := by
    unfold spectralRadialEvaluationWeight
    positivity
  have hwc : spectralRadialEvaluationWeight R hR δ ≤
      (1+spectralRadialEvaluationWeight R hR δ)^2 := by nlinarith
  have hs := hb.trans ((mul_le_mul_of_nonneg_right (hw.trans hwc) (sq_nonneg ‖u‖)))
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (by linarith) (norm_nonneg _))).mp
  simpa only [mul_pow] using hs

theorem spectralRadialSmoothApproximation_uniform (R δ : ℝ) (hR : 0 < R) (hδ : 0 < δ)
    (f : ℕ → 𝓢(ℝ,ℂ)) (u : SpectralRadialEnergy R)
    (hf : Tendsto (fun n => spectralRadialSmoothEmbedding R (f n)) atTop (𝓝 u)) :
    TendstoUniformlyOn (fun n r => f n r) (spectralRadialRepresentative R hR u) atTop (Icc δ R) := by
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  have hg : Tendsto (fun n => (1+spectralRadialEvaluationWeight R hR δ)*
      ‖spectralRadialSmoothEmbedding R (f n)-u‖) atTop (𝓝 0) := by
    have hu : Tendsto (fun _ : ℕ => u) atTop (𝓝 u) := tendsto_const_nhds
    have hc : Tendsto (fun _ : ℕ => 1+spectralRadialEvaluationWeight R hR δ) atTop
        (𝓝 (1+spectralRadialEvaluationWeight R hR δ)) := tendsto_const_nhds
    simpa only [sub_self,norm_zero,mul_zero] using hc.mul (hf.sub hu).norm
  filter_upwards [hg.eventually (Iio_mem_nhds hε)] with n hn r hr
  have hb := spectralRadialPointValue_annulus_bound R δ hR hδ r hr
    (spectralRadialSmoothEmbedding R (f n)-u)
  have hpos := hδ.trans_le hr.1
  rw [map_sub,spectralRadialPointValue_smooth R hR r hpos hr.2] at hb
  rw [dist_comm,dist_eq_norm,spectralRadialRepresentative,dite_eq_left hpos]
  exact hb.trans_lt hn

theorem spectralRadialRepresentative_continuousOn (R δ : ℝ) (hR : 0 < R) (hδ : 0 < δ)
    (u : SpectralRadialEnergy R) :
    ContinuousOn (spectralRadialRepresentative R hR u) (Icc δ R) := by
  obtain ⟨f,hf⟩ := spectralRadialSmoothApproximation R u
  exact (spectralRadialSmoothApproximation_uniform R δ hR hδ f u hf).continuousOn
    (Filter.Eventually.of_forall (fun n => (f n).continuous.continuousOn)).frequently

end DefocusingNLS

end OAI
