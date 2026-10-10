import OAI.Geometry.EinsteinFour.ChartMetricSmoothness
import OAI.Geometry.EinsteinFour.WeylDerivative

namespace OAI

/-! Metric compatibility for the actual coordinate tensor derivative. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped Manifold ContDiff BigOperators

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

def metricTensorCoordinates (g : SmoothMetric M) (c : M) (z : FourSpace) :
    CovariantCoordinates 2 := fun a => metricInChart g c z (a 0) (a 1)

theorem covariantDerivative_metricTensor (g : SmoothMetric M) (c : M) (z : FourSpace)
    (hG : IsUnit (metricInChart g c z).det) :
    covariantDerivative g c (metricTensorCoordinates g c) z = 0 := by
  funext a
  have hm := christoffel_metric_compatibility g c z hG (a 0) (a 1) (a 2)
  rw [Finset.sum_add_distrib] at hm
  have hfirst : (∑ b, christoffel g c z b (a 0) (a 1) *
      metricInChart g c z b (a 2)) =
      ∑ b, metricInChart g c z (a 2) b * christoffel g c z b (a 0) (a 1) := by
    apply Finset.sum_congr rfl
    intro b _
    rw [show metricInChart g c z b (a 2) = metricInChart g c z (a 2) b from g.symm _ _ _]
    ring
  have hsecond : (∑ b, christoffel g c z b (a 0) (a 2) *
      metricInChart g c z (a 1) b) =
      ∑ b, metricInChart g c z (a 1) b * christoffel g c z b (a 0) (a 2) := by
    apply Finset.sum_congr rfl
    intro b _
    ring
  simp only [covariantDerivative, metricTensorCoordinates, Fin.sum_univ_two]
  change partialDeriv (fun w => metricInChart g c w (a 1) (a 2)) (a 0) z -
    ((∑ b, christoffel g c z b (a 0) (a 1) * metricInChart g c z b (a 2)) +
     (∑ b, christoffel g c z b (a 0) (a 2) * metricInChart g c z (a 1) b)) = 0
  rw [hfirst, hsecond, ← hm]
  ring

end
end PositiveEinsteinFour.Geometry

end OAI
