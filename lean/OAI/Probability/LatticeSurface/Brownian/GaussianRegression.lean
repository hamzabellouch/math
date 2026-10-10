import Mathlib
import OAI.Probability.LatticeSurface.Brownian.GaussianTube

namespace OAI

namespace BrownianForcing

open MeasureTheory ProbabilityTheory Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E]

theorem gaussian_representer_tube (μ : Measure E) [IsGaussian μ]
    (hμ : (∫ x, x ∂μ) = 0) (L : StrongDual ℝ E) (g : E)
    (hg : ∀ M : StrongDual ℝ E, cov[L, M; μ] = M g)
    (hLg : 0 < L g) (ε : ℝ) (hε : 0 < ε) :
    0 < μ (Metric.ball g ε) := by
  let v : E := (L g)⁻¹ • g
  let R : E →L[ℝ] E := ContinuousLinearMap.id ℝ E - L.smulRight v
  have hL : HasGaussianLaw (fun x => L x) μ := by
    simpa using (IsGaussian.hasGaussianLaw_id (μ := μ)).map L
  have hR : HasGaussianLaw (fun x => R x) μ := by
    simpa using (IsGaussian.hasGaussianLaw_id (μ := μ)).map R
  have hvar : Var[L; μ] = L g := by
    rw [← covariance_self L.continuous.measurable.aemeasurable]; exact hg L
  have hRv (x : E) : R x = x - L x • v := rfl
  have hv : L g • v = g := by simp [v,smul_smul,hLg.ne']
  have hLM (M : StrongDual ℝ E) : cov[L, fun x => M (R x); μ] = 0 := by
    have he : (fun x => M (R x)) = (M : E → ℝ) - M v • (L : E → ℝ) := by
      funext x; simp [hRv,mul_comm]
    rw [he,covariance_sub_right hL.memLp_two
      (by simpa using ((IsGaussian.hasGaussianLaw_id (μ := μ)).map M).memLp_two)
      (hL.memLp_two.const_smul (M v)),covariance_smul_right,
      hg M,hg L]
    have : M v * L g = M g := by simp [v]; field_simp
    linarith
  have hj : HasGaussianLaw (fun x => (L x,R x)) μ := by
    convert! (IsGaussian.hasGaussianLaw_id (μ := μ)).map (L.prod R) using 1
  have hind : IndepFun (fun x => L x) (fun x => R x) μ := by
    apply hj.indepFun_of_covariance_strongDual
    intro M N
    have he : (M : ℝ → ℝ) ∘ (fun x => L x) = M 1 • (fun x => L x) := by
      funext x
      have := M.map_smul (L x) (1:ℝ)
      simpa [Function.comp_def,mul_comm] using this
    rw [he,covariance_smul_left]
    change M 1 * cov[L, (fun x => N (R x)); μ] = 0
    rw [hLM,mul_zero]
  let δ : ℝ := ε / (2*(‖v‖+1))
  have hδ : 0 < δ := div_pos hε (by positivity)
  have hδv : δ*‖v‖ ≤ ε/2 := by
    have hden : 0 < 2*(‖v‖+1) := by positivity
    rw [show δ*‖v‖ = ε*‖v‖/(2*(‖v‖+1)) by dsimp [δ]; ring]
    apply (div_le_iff₀ hden).mpr
    nlinarith [norm_nonneg v]
  have hpL : 0 < μ (L ⁻¹' Metric.ball (L g) δ) := by
    rw [← Measure.map_apply L.continuous.measurable measurableSet_ball,
      IsGaussian.map_eq_gaussianReal,hvar]
    exact (gaussianReal_absolutelyContinuous' _ (by simpa using hLg)).pos_mono
      (Metric.measure_ball_pos volume _ hδ)
  have hpR : 0 < μ (R ⁻¹' Metric.ball 0 (ε/2)) := by
    let : IsGaussian (μ.map R) := hR.isGaussian_map
    have hm : (∫ x, x ∂μ.map R) = 0 := by
      rw [integral_map R.continuous.measurable.aemeasurable (by fun_prop)]
      simpa only [id_eq,hμ,map_zero] using R.integral_comp_comm (IsGaussian.integrable_id (μ := μ))
    rw [← Measure.map_apply R.continuous.measurable measurableSet_ball]
    exact gaussian_small_ball _ hm _ (by linarith)
  have hpos : 0 < μ (L ⁻¹' Metric.ball (L g) δ ∩ R ⁻¹' Metric.ball 0 (ε/2)) := by
    rw [hind.measure_inter_preimage_eq_mul _ _ measurableSet_ball measurableSet_ball]
    exact ENNReal.mul_pos hpL.ne' hpR.ne'
  refine hpos.trans_le (measure_mono ?_)
  intro x hx
  rcases hx with ⟨hxL,hxR⟩
  change dist x g < ε
  rw [dist_eq_norm]
  have he : x-g = R x + (L x-L g) • v := by rw [hRv,sub_smul,hv]; abel
  rw [he]
  calc
    ‖R x+(L x-L g) • v‖ ≤ ‖R x‖ + ‖(L x-L g) • v‖ := norm_add_le _ _
    _ = ‖R x‖ + |L x-L g| * ‖v‖ := by rw [norm_smul,Real.norm_eq_abs]
    _ ≤ ‖R x‖ + δ*‖v‖ := by
      apply add_le_add_right
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      exact le_of_lt (by simpa [Metric.mem_ball,Real.dist_eq] using hxL)
    _ < ε := by
      have : ‖R x‖ < ε/2 := by simpa [Metric.mem_ball,dist_zero_right] using hxR
      linarith

end BrownianForcing

end OAI
