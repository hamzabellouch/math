import OAI.Geometry.EinsteinFour.OrientationCoverPathLift
import OAI.Geometry.EinsteinFour.OrientationCoverDeckMetric
import OAI.Geometry.EinsteinFour.MetricDoubleCover

namespace OAI

/-! The determinant-sign cover and its pullback metric form a metric double cover. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour
open scoped Manifold ContDiff ENNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

private theorem scaledEDistance_one_eq (g : SmoothMetric M) (x y : M) :
    scaledEDistance g 1 x y = metricEDistance g x y := by
  change ENNReal.ofReal (Real.sqrt 1) * metricEDistance g x y = _
  simp

def actualOrientationDoubleCover (g : SmoothMetric M) :
    MetricDoubleCover g (orientationCoverMetric g) where
  projection := orientationCoverProjection
  covering := orientationCover_isCoveringMap
  surjective := orientationCoverProjection_surjective
  deck := orientationCoverDeck
  involutive := orientationCoverDeck_deck
  free := orientationCoverDeck_free
  fibers := orientationCover_fibers
  deck_distance x y := by
    simp only [scaledEDistance_one_eq]
    exact orientationCover_deck_distance g x y
  distance_down x y := by
    simp only [scaledEDistance_one_eq]
    exact orientationCover_distance_down g x y
  distance_lift x y := by
    simp only [scaledEDistance_one_eq]
    exact orientationCover_distance_lift g x y

end
end PositiveEinsteinFour.Geometry

end OAI
