import OAI.Probability.InvariantIsing.Gaussian.GaussianConeCutoff

namespace OAI

/-! Finite-dimensional Gaussian variance for Lipschitz functions. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology
namespace InvariantIsing

lemma gaussian_centered_lipschitz_variance_le {d : ℕ} {L : ℝ≥0}
    {f : EuclideanSpace ℝ (Fin d) → ℝ} (hf : LipschitzWith L f) (h0 : f 0 = 0) :
    variance f (stdGaussian (EuclideanSpace ℝ (Fin d))) ≤ (L : ℝ)^2 := by
  let F := fun n : ℕ => gaussianConeCutoff L (2*(n+1 : ℝ)) f
  have hL n : LipschitzWith L (F n) := gaussianConeCutoff_lipschitz hf
  have hv n : variance (F n) (stdGaussian (EuclideanSpace ℝ (Fin d))) ≤ (L : ℝ)^2 :=
    gaussian_compact_variance_le (hL n) (gaussianConeCutoff_compact _ _ _)
  have ht (x : EuclideanSpace ℝ (Fin d)) : Tendsto (fun n => F n x) atTop (𝓝 (f x)) := by
    have he : ∀ᶠ n : ℕ in atTop, ‖x‖ ≤ (n : ℝ) :=
      tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop ‖x‖)
    apply tendsto_const_nhds.congr'
    filter_upwards [he] with n hn
    exact (gaussianConeCutoff_eq hf h0 x (by linarith)).symm
  have hm : Tendsto (fun n => ∫ x, F n x ∂stdGaussian _) atTop
      (𝓝 (∫ x, f x ∂stdGaussian _)) := by
    apply tendsto_integral_of_dominated_convergence (fun x => ‖f x‖)
      (fun n => (hL n).continuous.aestronglyMeasurable) (gaussian_lipschitz_integrable hf).norm
    · exact fun n => ae_of_all _ (gaussianConeCutoff_norm_le _ _ _)
    · exact ae_of_all _ ht
  exact variance_le_of_ae_tendsto_of_mean_tendsto
    (fun n => gaussian_lipschitz_memLp_two (hL n)) (gaussian_lipschitz_memLp_two hf)
    (ae_of_all _ ht) hm hv

/-- The Gaussian Poincaré inequality for globally Lipschitz observables. -/
theorem gaussianLipschitzVariance_proved : GaussianLipschitzVarianceInput := by
  intro d L f hf
  have hc : LipschitzWith L (fun x => f x-f 0) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simpa only [dist_eq_norm, sub_sub_sub_cancel_right] using hf.dist_le_mul x y
  have h := gaussian_centered_lipschitz_variance_le hc (by simp)
  rwa [variance_sub_const hf.continuous.aestronglyMeasurable] at h

end InvariantIsing

end

end OAI
