import OAI.Geometry.EinsteinFour.OrientationCoverSmoothLift
import OAI.Geometry.EinsteinFour.OrientationCoverDistanceDown

namespace OAI

/-! The sheet exchange is an actual smooth isometry for the pullback metric. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Bundle Set MeasureTheory
open scoped Manifold ContDiff ENNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem orientationCover_deck_smooth : ContMDiff I4 I4 ∞ (orientationCoverDeck (M := M)) := by
  apply contMDiff_orientationCover_lift continuous_orientationCoverDeck
  simpa only [Function.comp_def, orientationCoverDeck_proj] using
    (orientationCover_projection_smooth (M := M))

@[simp] theorem orientationCover_deck_mfderiv (x : OrientationCover M) :
    mfderiv I4 I4 orientationCoverDeck x = ContinuousLinearMap.id ℝ FourSpace := by
  have h := mfderiv_comp x
    (orientationCover_projection_hasMFDerivAt (orientationCoverDeck x)).mdifferentiableAt
    (orientationCover_deck_smooth.mdifferentiable (by simp) x)
  have he : orientationCoverProjection ∘ orientationCoverDeck =
      (orientationCoverProjection (M := M)) := rfl
  rw [he, orientationCover_projection_mfderiv, orientationCover_projection_mfderiv] at h
  exact h.symm

theorem orientationCover_deck_curve_length (g : SmoothMetric M)
    (γ : unitInterval → OrientationCover M) (hγ : ContMDiff (𝓡∂ 1) I4 1 γ) :
    (∫⁻ t, metricTangentENorm (orientationCoverMetric g) (orientationCoverDeck (γ t))
      (mfderiv (𝓡∂ 1) I4 (orientationCoverDeck ∘ γ) t 1)) =
    ∫⁻ t, metricTangentENorm (orientationCoverMetric g) (γ t)
      (mfderiv (𝓡∂ 1) I4 γ t 1) := by
  apply lintegral_congr
  intro t
  have h := mfderiv_comp t (orientationCover_deck_smooth.mdifferentiable (by simp) (γ t))
    (hγ.mdifferentiable one_ne_zero t)
  rw [orientationCover_deck_mfderiv] at h
  have hd : mfderiv (𝓡∂ 1) I4 (orientationCoverDeck ∘ γ) t =
      mfderiv (𝓡∂ 1) I4 γ t := h
  rw [hd, metricTangentENorm_eq_ofReal, metricTangentENorm_eq_ofReal,
    metricTangentNorm_eq_sqrt, metricTangentNorm_eq_sqrt]
  rfl

private theorem orientationCover_deck_distance_le (g : SmoothMetric M)
    (x y : OrientationCover M) :
    metricEDistance (orientationCoverMetric g) (orientationCoverDeck x) (orientationCoverDeck y) ≤
      metricEDistance (orientationCoverMetric g) x y := by
  rw [metricEDistance_eq_iInf (orientationCoverMetric g) x y]
  refine le_iInf fun γ => le_iInf fun hγ => ?_
  let δ : Path (orientationCoverDeck x) (orientationCoverDeck y) :=
    γ.map continuous_orientationCoverDeck
  have hδ : ContMDiff (𝓡∂ 1) I4 1 δ :=
    (orientationCover_deck_smooth.of_le (by simp)).comp hγ
  calc
    metricEDistance (orientationCoverMetric g) (orientationCoverDeck x) (orientationCoverDeck y) ≤
        ∫⁻ t, metricTangentENorm (orientationCoverMetric g) (δ t)
          (mfderiv (𝓡∂ 1) I4 δ t 1) := by
      rw [metricEDistance_eq_iInf]
      exact iInf_le_of_le δ (iInf_le _ hδ)
    _ = _ := orientationCover_deck_curve_length g γ hγ

theorem orientationCover_deck_distance (g : SmoothMetric M) (x y : OrientationCover M) :
    metricEDistance (orientationCoverMetric g) (orientationCoverDeck x) (orientationCoverDeck y) =
      metricEDistance (orientationCoverMetric g) x y := by
  apply le_antisymm (orientationCover_deck_distance_le g x y)
  simpa only [orientationCoverDeck_deck] using
    orientationCover_deck_distance_le g (orientationCoverDeck x) (orientationCoverDeck y)

end
end PositiveEinsteinFour.Geometry

end OAI
