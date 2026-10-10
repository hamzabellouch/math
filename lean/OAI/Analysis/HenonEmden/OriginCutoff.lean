import OAI.Analysis.HenonEmden.WeightedVirial

namespace OAI

universe uE

section OriginCutoff

open MeasureTheory Set Filter Topology Metric
open scoped InnerProductSpace
noncomputable section
namespace HenonLaneEmden
open WeakPDE Cutoff

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma compact_radialDir {ψ : E → ℝ} (hψ : HasCompactSupport ψ) :
    HasCompactSupport (fun x => dir ψ x x) := by
  apply HasCompactSupport.intro hψ
  intro x hx
  simp only [dir,fderiv_of_notMem_tsupport ℝ hx,zero_apply]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma compact_dilation_eventually_zero {ψ : E → ℝ} (hψ : HasCompactSupport ψ)
    {x : E} (hx : x ≠ 0) :
    (fun R : ℝ => ψ (R⁻¹ • x)) =ᶠ[𝓝[>] 0] 0 := by
  obtain ⟨M,hM⟩ := hψ.isBounded.exists_norm_le
  have he : 0 < ‖x‖/(max M 0+1) := div_pos (norm_pos_iff.mpr hx) (by positivity)
  filter_upwards [self_mem_nhdsWithin,(eventually_lt_nhds he).filter_mono nhdsWithin_le_nhds] with R hR hlt
  apply image_eq_zero_of_notMem_tsupport
  intro hs
  have hh := hM _ hs
  rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hR),← div_eq_inv_mul] at hh
  have hb : R*M < ‖x‖ := by
    have hr : R*(max M 0+1) < ‖x‖ := (lt_div_iff₀ (by positivity : 0 < max M 0+1)).mp hlt
    exact (mul_le_mul_of_nonneg_left (by linarith [le_max_left M 0] : M ≤ max M 0+1) hR.le).trans_lt hr
  exact (not_le_of_gt hb) (by nlinarith [(div_le_iff₀ hR).mp hh])

lemma integral_mul_dilation_tendsto_zero [Nontrivial E] {G ψ : E → ℝ}
    (hG : Integrable G) (hψ : Continuous ψ) (hψc : HasCompactSupport ψ) :
    Tendsto (fun R : ℝ => ∫ x, G x*ψ (R⁻¹ • x)) (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨M,hM⟩ := hψc.exists_bound_of_continuous hψ
  have hh := tendsto_integral_filter_of_dominated_convergence (μ := volume) (l := 𝓝[>] (0:ℝ))
    (F := fun R x => G x*ψ (R⁻¹ • x)) (f := fun _ => (0:ℝ)) (fun x => M*‖G x‖)
    (Eventually.of_forall fun R => hG.aestronglyMeasurable.mul
      (hψ.comp (continuous_const.smul continuous_id)).aestronglyMeasurable)
    (Eventually.of_forall fun R => ae_of_all _ fun x => by
      rw [norm_mul]; exact (mul_le_mul_of_nonneg_left (hM _) (norm_nonneg _)).trans_eq (mul_comm _ _))
    (hG.norm.const_mul M) ?_
  · simpa only [integral_zero] using hh
  filter_upwards [ae_iff.mpr (show volume {x : E | ¬x ≠ 0}=0 by simp)] with x hx
  apply tendsto_const_nhds.congr'
  filter_upwards [compact_dilation_eventually_zero hψc hx] with R hR
  simp [hR]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma radialDir_dilation {ψ : E → ℝ} (hψ : Differentiable ℝ ψ) (R : ℝ) (x : E) :
    dir (fun y => ψ (R⁻¹ • y)) x x = dir ψ (R⁻¹ • x) (R⁻¹ • x) := by
  have hh := (hψ (R⁻¹ • x)).hasFDerivAt.comp x
    ((hasFDerivAt_id x).const_smul R⁻¹)
  change HasFDerivAt (fun y => ψ (R⁻¹ • y)) _ x at hh
  rw [dir,hh.fderiv]
  rfl

end HenonLaneEmden
end
end OriginCutoff

end OAI
