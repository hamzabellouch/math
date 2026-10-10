import OAI.MeasureTheory.Falconer.Estimates.PositiveDistanceOriginalSpatial
import Mathlib.MeasureTheory.Integral.Bochner.Basic

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ENNReal

noncomputable def distanceDifferenceKernel (v : ℝ) (x : Fin 4 → Plane) : ℝ≥0∞ :=
  ENNReal.ofReal (1/(1+(2:ℝ)^v*|dist (x 0) (x 1)-dist (x 2) (x 3)|)^2)

theorem distanceDifferenceKernel_measurable (v : ℝ) : Measurable (distanceDifferenceKernel v) := by
  unfold distanceDifferenceKernel
  fun_prop

def fourPairGood (G H : Set (Plane × Plane)) : Set (Fin 4 → Plane) :=
  fourSpatialPairEquiv ⁻¹' (G ×ˢ H)

theorem measurable_fourPairGood {G H : Set (Plane × Plane)}
    (hG : MeasurableSet G) (hH : MeasurableSet H) : MeasurableSet (fourPairGood G H) :=
  (hG.prod hH).preimage fourSpatialPairEquiv.measurable

theorem enorm_setIntegral_le_good_kernel (μ : Measure (Fin 4 → Plane))
    (S G : Set (Fin 4 → Plane)) (hG : MeasurableSet G)
    (F : (Fin 4 → Plane) → ℂ) (K : (Fin 4 → Plane) → ℝ≥0∞) (c : ℝ≥0∞) (hc : c ≠ ∞)
    (hb : ∀ᵐ x ∂μ.restrict S, ‖F x‖ₑ ≤ c*K x)
    (hs : ∀ᵐ x ∂μ.restrict S, F x ≠ 0 → x ∈ G) :
    ‖∫ x in S, F x ∂μ‖ₑ ≤ c*(∫⁻ x in S ∩ G, K x ∂μ) := by
  apply (enorm_integral_le_lintegral_enorm F).trans
  calc
    (∫⁻ x in S, ‖F x‖ₑ ∂μ) ≤ ∫⁻ x in S, c*G.indicator K x ∂μ := by
      apply lintegral_mono_ae
      filter_upwards [hb,hs] with x hx hxs
      by_cases h : F x = 0
      · simp only [h,enorm_zero]; exact zero_le
      · rw [Set.indicator_of_mem (hxs h)]
        exact hx
    _ = c*(∫⁻ x in S ∩ G, K x ∂μ) := by
      rw [lintegral_const_mul' c _ hc,lintegral_indicator hG,Measure.restrict_restrict hG]
      rw [inter_comm]

namespace PositiveDistanceData

theorem original_complex_kernel_max (d e : PositiveDistanceData)
    [IsFiniteMeasure d.ρ] [IsFiniteMeasure e.ρ]
    (ht : d.t = e.t) (hn : d.normalization = e.normalization)
    (S : Set (Fin 4 → Plane)) (hS : MeasurableSet S)
    (F : (Fin 4 → Plane) → ℂ) {H : ℝ} (hH : 0 ≤ H)
    (hb : ∀ᵐ x ∂(Measure.pi (fourCells d e)).restrict S,
      ‖F x‖ ≤ H*(2:ℝ)^(-((d.t:ℝ)-d.a)) /
        (1+(2:ℝ)^d.t*|dist (x 0) (x 1)-dist (x 2) (x 3)|)^2)
    (hs : ∀ᵐ x ∂(Measure.pi (fourCells d e)).restrict S,
      F x ≠ 0 → (x 0,x 1) ∈ d.good ∧ (x 2,x 3) ∈ e.good) :
    ‖∫ x in S, F x ∂Measure.pi (fourCells d e)‖ₑ ≤
      ENNReal.ofReal H * binKernelConstant *
        ENNReal.ofReal (d.levelMass^4*(2:ℝ)^(-2*((d.t:ℝ)-d.a))) *
        max d.coincidence e.coincidence := by
  have hg := enorm_setIntegral_le_good_kernel (Measure.pi (fourCells d e)) S
    (fourPairGood d.good e.good) (measurable_fourPairGood d.measurable_good e.measurable_good)
    F (distanceDifferenceKernel d.t)
    (ENNReal.ofReal H*ENNReal.ofReal ((2:ℝ)^(-((d.t:ℝ)-d.a)))) (by finiteness) (by
      filter_upwards [hb] with x hx
      rw [← ofReal_norm]
      have hh := ENNReal.ofReal_le_ofReal hx
      convert hh using 1
      dsimp [distanceDifferenceKernel]
      rw [← ENNReal.ofReal_mul hH,← ENNReal.ofReal_mul (mul_nonneg hH (by positivity))]
      rw [Real.rpow_natCast]
      congr 1
      ring) hs
  let T := fourSpatialPairEquiv.symm ⁻¹' S
  have hT : MeasurableSet T := hS.preimage fourSpatialPairEquiv.symm.measurable
  have he : S ∩ fourPairGood d.good e.good =
      fourSpatialPairEquiv ⁻¹' (T ∩ (d.good ×ˢ e.good)) := by
    ext x
    simp only [T,mem_inter_iff,mem_preimage,fourPairGood,
      MeasurableEquiv.symm_apply_apply]
  rw [he,mul_assoc] at hg
  apply hg.trans
  have hh := mul_le_mul_right (original_spatial_kernel_max d e ht hn T hT) (ENNReal.ofReal H)
  simpa only [distanceDifferenceKernel,Real.rpow_natCast,mul_assoc] using hh

end PositiveDistanceData

end PlanarFalconer

end OAI
