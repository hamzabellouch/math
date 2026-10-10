import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimitiveKernelBound

namespace OAI

/-! Dominated convergence of the actual truncated scalar kernel on the quotient. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace CubicFirstMoment

lemma cubicThetaRankin_exponent_tendsto :
    Tendsto (fun σ : ℝ => 2+2*σ) (𝓝[>] 0) (𝓝[>] 2) := by
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · have h : ContinuousAt (fun σ : ℝ => 2+2*σ) 0 := by fun_prop
    simpa using h.tendsto.mono_left (show 𝓝[>] (0:ℝ) ≤ 𝓝 0 from nhdsWithin_le_nhds)
  · filter_upwards [self_mem_nhdsWithin] with σ hσ
    change 0<σ at hσ
    change 2<2+2*σ
    linarith

theorem cubicThetaScalarRankinKernel_uniform :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ σ : ℝ in 𝓝[>] 0,
      ∀ q : CubicThetaQuotient, ‖(σ:ℂ)*(cubicThetaScalarRankinKernel σ q:ℂ)‖ ≤ K := by
  obtain ⟨K,hK,hbound⟩ := cubicThetaPrimitiveKernel_uniform
  refine ⟨K,hK,?_⟩
  filter_upwards [cubicThetaRankin_exponent_tendsto.eventually hbound,
    self_mem_nhdsWithin] with σ hb hσ
  change 0<σ at hσ
  intro q
  let p := cubicThetaBorelSection q
  have hsc := cubicThetaScalarHeightCutoff_le_primitive p.property
    (show 2<2+2*σ by linarith)
  have hnonneg := cubicThetaScalarRankinKernel_nonneg σ q
  have hsmall := mul_le_mul_of_nonneg_left hsc hσ.le
  have hbig := hb p.val p.property
  change σ*cubicThetaScalarRankinKernel σ q ≤ σ*cubicThetaPrimitiveKernel p.val (2+2*σ) at hsmall
  rw [←Complex.ofReal_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg hσ.le hnonneg)]
  nlinarith

theorem cubicThetaScalarRankinKernel_integral_limit
    (F : CubicThetaQuotient → ℂ) (hF : Integrable F cubicThetaQuotientMeasure) :
    Tendsto (fun σ : ℝ => ∫ q,(σ:ℂ)*(cubicThetaScalarRankinKernel σ q:ℂ)*F q
        ∂cubicThetaQuotientMeasure) (𝓝[>] 0)
      (𝓝 (((Real.pi:ℂ)^2/(108*principalIdealZeta 2))*
        ∫ q,F q ∂cubicThetaQuotientMeasure)) := by
  obtain ⟨K,hK,hbound⟩ := cubicThetaScalarRankinKernel_uniform
  rw [←integral_const_mul]
  apply tendsto_integral_filter_of_dominated_convergence (fun q => K*‖F q‖)
  · apply Filter.Eventually.of_forall
    intro σ
    have hm : Measurable (fun q => (σ:ℂ)*(cubicThetaScalarRankinKernel σ q:ℂ)) := by
      exact measurable_const.mul (Complex.continuous_ofReal.measurable.comp
        (cubicThetaScalarRankinKernel_measurable σ))
    exact hm.aestronglyMeasurable.mul hF.aestronglyMeasurable
  · filter_upwards [hbound] with σ hσ
    exact Filter.Eventually.of_forall (fun q => by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (hσ q) (_root_.norm_nonneg _))
  · exact hF.norm.const_mul K
  · exact Filter.Eventually.of_forall (fun q =>
      (cubicThetaScalarRankinKernel_residue q).mul tendsto_const_nhds)

end CubicFirstMoment

end

end OAI
