import Mathlib
import OAI.Probability.GaussianRegression.Main
import OAI.Probability.MemoryPrecision.BallAverages

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter EuclideanGeometry
open scoped ENNReal NNReal RealInnerProductSpace Topology Pointwise

noncomputable section
universe u v

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology Pointwise
namespace MemoryPrecision
open NoiselessRegression

lemma gaussianKernel_translated_ball_mixture (m : ℕ) (hm : 1 ≤ m) {δ : ℝ} (hδ : 0 < δ)
    (y x : Space m) :
    ENNReal.ofReal (GaussianKernel m δ (y-x)) =
      ∫⁻ r in Ioi 0, (Metric.ball y r).indicator
        (fun _ => ENNReal.ofReal ((r/δ^2)*GaussianKernel m δ (r • CoordinateUnit m))) x := by
  rw [gaussianKernel_ball_mixture m hm hδ]
  apply lintegral_congr
  intro r
  have he : y-x ∈ Metric.ball (0 : Space m) r ↔ x ∈ Metric.ball y r := by
    simp only [Metric.mem_ball, dist_eq_norm, sub_zero, norm_sub_rev]
  by_cases hx : x ∈ Metric.ball y r
  · rw [Set.indicator_of_mem (he.mpr hx), Set.indicator_of_mem hx]
  · rw [Set.indicator_of_notMem (mt he.mp hx), Set.indicator_of_notMem hx]

def GaussianConvolution {m : ℕ} (ν : Measure (Space m)) (δ : ℝ) (y : Space m) : ℝ :=
  ∫ x, GaussianKernel m δ (y-x) ∂ν

lemma gaussianConvolution_shell {m : ℕ} (hm : 1 ≤ m) (ν : Measure (Space m))
    [IsFiniteMeasure ν] {δ : ℝ} (hδ : 0 < δ) (y : Space m) :
    GaussianConvolution ν δ y = ∫ r in Ioi 0,
      ((r/δ^2)*GaussianKernel m δ (r • CoordinateUnit m)) * (ν (Metric.ball y r)).toReal := by
  have hk : Measurable (GaussianKernel m δ) := (gaussianKernel_continuous m δ).measurable
  have hmeas : Measurable (fun z : Space m × ℝ =>
      (Metric.ball y z.2).indicator
        (fun _ => ENNReal.ofReal ((z.2/δ^2)*GaussianKernel m δ (z.2 • CoordinateUnit m))) z.1) := by
    have he : (fun z : Space m × ℝ => (Metric.ball y z.2).indicator
        (fun _ => ENNReal.ofReal ((z.2/δ^2)*GaussianKernel m δ (z.2 • CoordinateUnit m))) z.1) =
      {z : Space m × ℝ | dist z.1 y < z.2}.indicator
        (fun z => ENNReal.ofReal ((z.2/δ^2)*GaussianKernel m δ (z.2 • CoordinateUnit m))) := by
      ext z
      by_cases hz : z.1 ∈ Metric.ball y z.2
      · rw [Set.indicator_of_mem hz, Set.indicator_of_mem
          (show z ∈ {z : Space m × ℝ | dist z.1 y < z.2} from hz)]
      · rw [Set.indicator_of_notMem hz, Set.indicator_of_notMem
          (show z ∉ {z : Space m × ℝ | dist z.1 y < z.2} from hz)]
    rw [he]
    exact (by fun_prop : Measurable (fun z : Space m × ℝ =>
      ENNReal.ofReal ((z.2/δ^2)*GaussianKernel m δ (z.2 • CoordinateUnit m)))).indicator
      (measurableSet_lt (by fun_prop) (by fun_prop))
  unfold GaussianConvolution
  rw [integral_eq_lintegral_of_nonneg_ae
    (Eventually.of_forall (fun _ => gaussianKernel_nonneg m δ _))
    ((hk.comp (by fun_prop)).aestronglyMeasurable)]
  simp_rw [gaussianKernel_translated_ball_mixture m hm hδ y]
  rw [lintegral_lintegral_swap hmeas.aemeasurable]
  simp_rw [lintegral_indicator Metric.isOpen_ball.measurableSet, setLIntegral_const]
  have hmass : Measurable (fun r : ℝ => (ν (Metric.ball y r)).toReal) :=
    (show Monotone (fun r : ℝ => ν (Metric.ball y r)) from
      fun a b h => measure_mono (Metric.ball_subset_ball h)).measurable.ennreal_toReal
  rw [integral_eq_lintegral_of_nonneg_ae
    ((ae_restrict_mem measurableSet_Ioi).mono (fun r hr =>
      mul_nonneg (mul_nonneg (div_nonneg hr.le (sq_nonneg δ)) (gaussianKernel_nonneg m δ _))
        ENNReal.toReal_nonneg)) (by fun_prop)]
  congr 1
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
  rw [ENNReal.ofReal_mul (mul_nonneg (div_nonneg hr.le (sq_nonneg δ))
    (gaussianKernel_nonneg m δ _)), ENNReal.ofReal_toReal (measure_ne_top _ _)]

lemma gaussianConvolution_mixture {m : ℕ} (hm : 1 ≤ m) (ν : Measure (Space m))
    [IsFiniteMeasure ν] {δ : ℝ} (hδ : 0 < δ) (y : Space m) :
    GaussianConvolution ν δ y = ∫ r in Ioi 0, RadialMixture m δ r * BallAverage ν y r := by
  rw [gaussianConvolution_shell hm ν hδ y]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
  have hr0 : 0 < r := hr
  unfold RadialMixture BallAverage
  field_simp [(unitBallVolume_pos m).ne', hr0.ne']

lemma gaussianConvolution_scaled_mixture {m : ℕ} (hm : 1 ≤ m) (ν : Measure (Space m))
    [IsFiniteMeasure ν] {δ : ℝ} (hδ : 0 < δ) (y : Space m) :
    GaussianConvolution ν δ y = ∫ r in Ioi 0, RadialMixture m 1 r * BallAverage ν y (δ*r) := by
  rw [gaussianConvolution_mixture hm ν hδ y]
  have he := integral_comp_mul_left_Ioi'
    (fun r => RadialMixture m δ r * BallAverage ν y r) 0 hδ
  simp only [mul_zero, smul_eq_mul] at he
  rw [← he, ← integral_const_mul]
  apply integral_congr_ae
  exact Eventually.of_forall (fun radius => by
    dsimp only
    rw [radialMixture_scale m hδ]
    field_simp [hδ.ne'])

lemma ae_tendsto_gaussianConvolution {m : ℕ} (hm : 1 ≤ m) (ν : Measure (Space m))
    [IsFiniteMeasure ν] (hν : ν ≪ volume) :
    ∀ᵐ y ∂(volume : Measure (Space m)), Tendsto (fun δ : ℝ => GaussianConvolution ν δ y)
      (𝓝[>] (0:ℝ)) (𝓝 ((ν.rnDeriv volume y).toReal)) := by
  filter_upwards [ae_tendsto_ballAverage hm ν hν] with y hy
  apply (tendsto_radial_average hm ν y ENNReal.toReal_nonneg hy).congr'
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  exact (gaussianConvolution_scaled_mixture hm ν hδ y).symm
end MemoryPrecision


end

end OAI
