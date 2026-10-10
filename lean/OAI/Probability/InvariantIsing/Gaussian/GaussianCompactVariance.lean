import OAI.Probability.InvariantIsing.Gaussian.GaussianTestVariance
import OAI.Probability.InvariantIsing.Gaussian.GaussianSmoothing
import OAI.Probability.InvariantIsing.Pressure.VarianceLimit

namespace OAI

/-! Extending Gaussian Poincare from smooth to compact Lipschitz tests. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology
namespace InvariantIsing

def gaussianApproxBump (d n : ℕ) : ContDiffBump (0 : EuclideanSpace ℝ (Fin d)) where
  rIn := (1/(n+1 : ℝ))/2
  rOut := 1/(n+1 : ℝ)
  rIn_pos := by positivity
  rIn_lt_rOut := by
    have h : 0 < 1/(n+1 : ℝ) := by positivity
    linarith

lemma gaussianApproxBump_rOut_le (d n : ℕ) : (gaussianApproxBump d n).rOut ≤ 1 := by
  change 1/(n+1 : ℝ) ≤ 1
  apply (div_le_one (by positivity)).mpr
  linarith [Nat.cast_nonneg (α := ℝ) n]

theorem gaussian_compact_variance_le {d : ℕ} {L : ℝ≥0}
    {f : EuclideanSpace ℝ (Fin d) → ℝ} (hf : LipschitzWith L f)
    (hc : HasCompactSupport f) :
    variance f (stdGaussian (EuclideanSpace ℝ (Fin d))) ≤ (L : ℝ)^2 := by
  let F := fun n => gaussianSmooth (gaussianApproxBump d n) f
  have hL n : LipschitzWith L (F n) := gaussianSmooth_lipschitz _ hf
  have hv n : variance (F n) (stdGaussian (EuclideanSpace ℝ (Fin d))) ≤ (L : ℝ)^2 :=
    gaussian_test_variance_le (gaussianSmooth_test _ hf hc) (hL n)
  have ht (x : EuclideanSpace ℝ (Fin d)) : Tendsto (fun n => F n x) atTop (𝓝 (f x)) := by
    exact ContDiffBump.convolution_tendsto_right_of_continuous
      (show Tendsto (fun n => (gaussianApproxBump d n).rOut) atTop (𝓝 0) from
        tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)) hf.continuous x
  obtain ⟨B, hB⟩ := hc.exists_bound_of_continuous hf.continuous
  have hbound n x : ‖F n x‖ ≤ B+(L : ℝ) := by
    calc
      _ ≤ ‖f x‖+dist (F n x) (f x) := by
        simpa only [add_sub_cancel, dist_eq_norm] using norm_add_le (f x) (F n x-f x)
      _ ≤ B+(L : ℝ)*(gaussianApproxBump d n).rOut :=
        add_le_add (hB x) (gaussianSmooth_dist_le _ hf x)
      _ ≤ B+(L : ℝ) := by
        nlinarith [mul_le_mul_of_nonneg_left (gaussianApproxBump_rOut_le d n) L.coe_nonneg]
  have hm : Tendsto (fun n => ∫ x, F n x ∂stdGaussian _) atTop
      (𝓝 (∫ x, f x ∂stdGaussian _)) := by
    apply tendsto_integral_of_dominated_convergence (fun _ => B+(L : ℝ))
      (fun n => (hL n).continuous.aestronglyMeasurable) (integrable_const _)
    · exact fun n => ae_of_all _ (hbound n)
    · exact ae_of_all _ ht
  exact variance_le_of_ae_tendsto_of_mean_tendsto
    (fun n => gaussian_lipschitz_memLp_two (hL n)) (gaussian_lipschitz_memLp_two hf)
    (ae_of_all _ ht) hm hv

end InvariantIsing

end

end OAI
