import Mathlib

namespace OAI

namespace BrownianForcing

open MeasureTheory ProbabilityTheory Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E]

theorem gaussian_small_ball (μ : Measure E) [IsGaussian μ]
    (hμ : (∫ x, x ∂μ) = 0) (ε : ℝ) (hε : 0 < ε) :
    0 < μ (Metric.ball 0 ε) := by
  obtain ⟨x,hx⟩ := μ.nonempty_support (by exact MeasureTheory.IsProbabilityMeasure.ne_zero μ)
  have hx' : 0 < μ (Metric.ball x (ε/4)) :=
    (Measure.mem_support_iff_forall x).mp hx _ (Metric.ball_mem_nhds _ (by linarith))
  let T : E × E →L[ℝ] E := (ContinuousLinearMap.snd ℝ E E).comp
    (ContinuousLinearMap.rotation (Real.pi/4))
  have hmap : (μ.prod μ).map T = μ := by
    rw [show (T : E × E → E) = Prod.snd ∘ ContinuousLinearMap.rotation (Real.pi/4) from rfl,
      ← Measure.map_map (by fun_prop) (by fun_prop),
      IsGaussian.map_rotation_eq_self (by simpa using hμ), Measure.map_snd_prod]
    simp
  have hsub : Metric.ball x (ε/4) ×ˢ Metric.ball x (ε/4) ⊆ T ⁻¹' Metric.ball 0 ε := by
    rintro ⟨y,z⟩ ⟨hy,hz⟩
    change dist (T (y,z)) 0 < ε
    rw [dist_zero_right]
    have hT : T (y,z) = Real.cos (Real.pi/4) • (z-y) := by
      dsimp [T]
      rw [ContinuousLinearMap.rotation_apply]
      simp only [Real.cos_pi_div_four,Real.sin_pi_div_four]
      module
    rw [hT,norm_smul]
    have hc : ‖Real.cos (Real.pi/4)‖ ≤ 1 := by simpa only [Real.norm_eq_abs] using Real.abs_cos_le_one (Real.pi/4)
    calc
      ‖Real.cos (Real.pi/4)‖ * ‖z-y‖ ≤ ‖z-y‖ := mul_le_of_le_one_left (norm_nonneg _) hc
      _ ≤ ‖z-x‖+‖y-x‖ := by simpa only [dist_eq_norm] using dist_triangle_right z y x
      _ < ε := by
        rw [Metric.mem_ball,dist_eq_norm] at hy hz
        linarith
  calc
    0 < (μ.prod μ) (Metric.ball x (ε/4) ×ˢ Metric.ball x (ε/4)) := by
      rw [Measure.prod_prod]; exact ENNReal.mul_pos hx'.ne' hx'.ne'
    _ ≤ (μ.prod μ) (T ⁻¹' Metric.ball 0 ε) := measure_mono hsub
    _ = μ (Metric.ball 0 ε) := by
      rw [← Measure.map_apply T.continuous.measurable measurableSet_ball,hmap]

end BrownianForcing

end OAI
