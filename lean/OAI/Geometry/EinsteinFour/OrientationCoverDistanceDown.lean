import OAI.Geometry.EinsteinFour.OrientationCoverMetric
import OAI.Geometry.EinsteinFour.MetricDistance

namespace OAI

/-! Projection preserves the length of every differentiable path, hence cannot
increase the actual Riemannian distance. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Bundle Set MeasureTheory
open scoped Manifold ContDiff ENNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem orientationCover_curve_derivative (γ : unitInterval → OrientationCover M)
    (hγ : ContMDiff (𝓡∂ 1) I4 1 γ) (t : unitInterval) :
    mfderiv (𝓡∂ 1) I4 (orientationCoverProjection ∘ γ) t =
      mfderiv (𝓡∂ 1) I4 γ t := by
  have h := mfderiv_comp t
    (orientationCover_projection_hasMFDerivAt (γ t)).mdifferentiableAt
    (hγ t |>.mdifferentiableAt one_ne_zero)
  rw [orientationCover_projection_mfderiv] at h
  exact h

theorem orientationCover_curve_length (g : SmoothMetric M)
    (γ : unitInterval → OrientationCover M) (hγ : ContMDiff (𝓡∂ 1) I4 1 γ) :
    (∫⁻ t, metricTangentENorm g ((γ t).proj)
      (mfderiv (𝓡∂ 1) I4 (orientationCoverProjection ∘ γ) t 1)) =
    ∫⁻ t, metricTangentENorm (orientationCoverMetric g) (γ t)
      (mfderiv (𝓡∂ 1) I4 γ t 1) := by
  apply lintegral_congr
  intro t
  rw [orientationCover_curve_derivative γ hγ t, metricTangentENorm_eq_ofReal,
    metricTangentENorm_eq_ofReal, metricTangentNorm_eq_sqrt, metricTangentNorm_eq_sqrt]
  rfl

theorem orientationCover_distance_down (g : SmoothMetric M) (x y : OrientationCover M) :
    metricEDistance g x.proj y.proj ≤ metricEDistance (orientationCoverMetric g) x y := by
  rw [metricEDistance_eq_iInf (orientationCoverMetric g) x y]
  refine le_iInf fun γ => le_iInf fun hγ => ?_
  let δ : Path x.proj y.proj := γ.map orientationCover_isCoveringMap.continuous
  have hδ : ContMDiff (𝓡∂ 1) I4 1 δ :=
    (orientationCover_projection_smooth.of_le (by simp)).comp hγ
  calc
    metricEDistance g x.proj y.proj ≤
        ∫⁻ t, metricTangentENorm g (δ t) (mfderiv (𝓡∂ 1) I4 δ t 1) := by
      rw [metricEDistance_eq_iInf]
      exact iInf_le_of_le δ (iInf_le _ hδ)
    _ = ∫⁻ t, metricTangentENorm (orientationCoverMetric g) (γ t)
        (mfderiv (𝓡∂ 1) I4 γ t 1) := orientationCover_curve_length g γ hγ

end
end PositiveEinsteinFour.Geometry

end OAI
