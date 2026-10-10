import Mathlib
import OAI.Geometry.TamingCompatibility.DifferentialForms.MetricOperatorInner

namespace OAI

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open NormalMetricCalculus ManifoldHodge
open scoped Manifold ContDiff RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]

lemma actual_principal (J : AlmostComplexStructure X) (α : TwoForm X)
    (ht : Tames α J) (p : X) (D : GeometricChart.Data J α ht p)
    {x : Space} (hx : x ∈ D.domain) (i j : Fin 4) :
    NormalMetricCalculus.principal (coordinateMetric J α ht p x).bilinear i j =
      GeometricChart.normalMetric J α ht p D i j x := by
  exact principal_eq_frame _ _ (D.frame_gram x hx) i j

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end

end OAI
