import Mathlib

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling.CompactExpectation
open Set MeasureTheory Filter Function
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [IsFiniteMeasureOnCompacts μ]

lemma hasDerivAt_setIntegral {f : ℝ × E → ℝ} (hf : ContDiff ℝ 1 f)
    {K : Set E} (hK : IsCompact K) (t : ℝ) :
    HasDerivAt (fun t => ∫y in K,f (t,y) ∂μ)
      (∫y in K,fderiv ℝ f (t,y) (1,0) ∂μ) t := by
  let D := fun p : ℝ × E => fderiv ℝ f p (1,0)
  have hD : Continuous D := (hf.continuous_fderiv (by norm_num)).clm_apply continuous_const
  obtain ⟨C,hC⟩ := ((isCompact_closedBall t 1).prod hK).exists_bound_of_continuousOn hD.continuousOn
  have hh := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ:=μ.restrict K)
    (F:=fun t y => f (t,y)) (F':=fun t y => D (t,y))
    (Metric.ball_mem_nhds t zero_lt_one)
    (Eventually.of_forall fun s => (hf.continuous.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable)
    ((hf.continuous.comp (continuous_const.prodMk continuous_id)).continuousOn.integrableOn_compact hK)
    ((hD.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable)
    (by
      filter_upwards [ae_restrict_mem hK.measurableSet] with y hy s hs
      exact hC (s,y) ⟨Metric.ball_subset_closedBall hs,hy⟩)
    (integrableOn_const (μ:=μ) hK.measure_ne_top)
    (by
      filter_upwards [] with y s _hs
      exact (hf.differentiable (by norm_num) (s,y)).hasFDerivAt.comp_hasDerivAt s
        ((hasDerivAt_id s).prodMk (hasDerivAt_const s y)))
  exact hh.2

theorem compact_test_hasDerivAt {A : ℝ × E → ℝ} (hA : ContDiff ℝ 1 A)
    {φ : E → ℝ} (hφ : ContDiff ℝ 1 φ) (hφc : HasCompactSupport φ) (t : ℝ) :
    HasDerivAt (fun t => ∫y,A (t,y)*φ y ∂μ)
      (∫y,(fderiv ℝ A (t,y) (1,0))*φ y ∂μ) t := by
  let B := fun p : ℝ × E => A p*φ p.2
  have hB : ContDiff ℝ 1 B := hA.mul (hφ.comp contDiff_snd)
  have hD (s : ℝ) (y : E) : fderiv ℝ B (s,y) (1,0)=fderiv ℝ A (s,y) (1,0)*φ y := by
    have hd := (hA.differentiable (by norm_num) (s,y)).hasFDerivAt.mul
      ((hφ.differentiable (by norm_num) y).hasFDerivAt.comp (s,y)
        (ContinuousLinearMap.snd ℝ ℝ E).hasFDerivAt)
    change HasFDerivAt B _ _ at hd
    rw [hd.fderiv]
    simp [ContinuousLinearMap.snd,mul_comm]
  have he (s : ℝ) : (∫y in tsupport φ,B (s,y) ∂μ)=∫y,A (s,y)*φ y ∂μ := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro y hy
    simp only [B,image_eq_zero_of_notMem_tsupport hy,mul_zero]
  have hg : (∫y in tsupport φ,fderiv ℝ B (t,y) (1,0) ∂μ)=
      ∫y,fderiv ℝ A (t,y) (1,0)*φ y ∂μ := by
    simp only [hD]
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro y hy
    simp only [image_eq_zero_of_notMem_tsupport hy,mul_zero]
  simpa only [he,hg] using hasDerivAt_setIntegral (μ:=μ) hB hφc t
end LogConcaveSampling.CompactExpectation

end

end

end

end OAI
