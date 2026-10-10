import OAI.Geometry.EinsteinFour.OrientationCoverSmoothLift
import OAI.Geometry.EinsteinFour.OrientationCoverDistanceDown
import Mathlib.Topology.Homotopy.Lifting

namespace OAI

/-! Smooth paths lift through the actual cover without changing length. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Bundle Set MeasureTheory
open scoped Manifold ContDiff ENNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem exists_orientationCover_path_lift (x : OrientationCover M) {b : M}
    (γ : Path x.proj b) (hγ : ContMDiff (𝓡∂ 1) I4 1 γ) :
    ∃ z : OrientationCover M, z.proj = b ∧ ∃ δ : Path x z,
      ContMDiff (𝓡∂ 1) I4 1 δ ∧ orientationCoverProjection ∘ δ = γ := by
  let C := orientationCover_isCoveringMap (M := M)
  let Γ := C.liftPath γ.toContinuousMap x γ.source
  have he : orientationCoverProjection ∘ Γ = γ := C.liftPath_lifts γ.toContinuousMap x γ.source
  let δ : Path x (Γ 1) := ⟨Γ, C.liftPath_zero γ.toContinuousMap x γ.source, rfl⟩
  refine ⟨Γ 1, ?_, δ, ?_, he⟩
  · exact (congrFun he 1).trans γ.target
  · apply contMDiff_orientationCover_lift Γ.continuous
    change ContMDiff (𝓡∂ 1) I4 1 (orientationCoverProjection ∘ Γ)
    rwa [he]

theorem orientationCover_min_distance_le (g : SmoothMetric M) (x y : OrientationCover M) :
    min (metricEDistance (orientationCoverMetric g) x y)
      (metricEDistance (orientationCoverMetric g) x (orientationCoverDeck y)) ≤
      metricEDistance g x.proj y.proj := by
  rw [metricEDistance_eq_iInf g x.proj y.proj]
  refine le_iInf fun γ => le_iInf fun hγ => ?_
  obtain ⟨z, hz, δ, hδ, he⟩ := exists_orientationCover_path_lift x γ hγ
  have hdist : metricEDistance (orientationCoverMetric g) x z ≤
      ∫⁻ t, metricTangentENorm (orientationCoverMetric g) (δ t)
        (mfderiv (𝓡∂ 1) I4 δ t 1) := by
    rw [metricEDistance_eq_iInf]
    exact iInf_le_of_le δ (iInf_le _ hδ)
  have hlen := orientationCover_curve_length g δ hδ
  change (∫⁻ t, metricTangentENorm g ((orientationCoverProjection ∘ δ) t)
    (mfderiv (𝓡∂ 1) I4 (orientationCoverProjection ∘ δ) t 1)) = _ at hlen
  rw [he] at hlen
  have hbound := hdist.trans_eq hlen.symm
  rcases (orientationCover_fibers z y).mp hz with rfl | rfl
  · exact (min_le_left _ _).trans hbound
  · exact (min_le_right _ _).trans hbound

theorem orientationCover_distance_lift (g : SmoothMetric M) (x y : OrientationCover M) :
    ∃ z : OrientationCover M, z.proj = y.proj ∧
      metricEDistance (orientationCoverMetric g) x z ≤ metricEDistance g x.proj y.proj := by
  have h := orientationCover_min_distance_le g x y
  by_cases hd : metricEDistance (orientationCoverMetric g) x y ≤
      metricEDistance (orientationCoverMetric g) x (orientationCoverDeck y)
  · exact ⟨y, rfl, (min_eq_left hd) ▸ h⟩
  · exact ⟨orientationCoverDeck y, rfl, (min_eq_right (le_of_not_ge hd)) ▸ h⟩

end
end PositiveEinsteinFour.Geometry

end OAI
