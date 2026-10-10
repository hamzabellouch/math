import OAI.Geometry.Relativity.CKS.ComparatorDefinitions
import OAI.Geometry.Relativity.CKS.BoundaryCharts

namespace OAI

noncomputable section
open Set Manifold Bundle Filter
open scoped ContDiff Topology
namespace CKSBoundarySurface
attribute [local instance] Classical.propDecidable
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H3 M]
  [@IsManifold ℝ _ E3 _ _ H3
    (@instTopologicalSpaceEuclideanHalfSpace 3 halfSpaceDimension_neZero) I3 ∞ M _ _]
lemma liftHalf_drop_chart (x : M) (y : Boundary M) (hy : y.val ∈ (chartAt H3 x).source) :
    liftHalf (dropPlane (I3 (chartAt H3 x y.val))) = chartAt H3 x y.val := by
  apply Subtype.ext
  exact lift_drop ((boundary_iff_zero x y.val hy).mp y.property)

lemma boundaryInverse_mem (x : Boundary M) {z : E2}
    (hz : liftHalf z ∈ (chartAt H3 x.val).target) :
    (chartAt H3 x.val).symm (liftHalf z) ∈ Boundary M :=
  chart_inverse_boundary x.val hz

lemma boundaryInverse_val (x : Boundary M) {z : E2}
    (hz : liftHalf z ∈ (chartAt H3 x.val).target) :
    (boundaryInverse x z).val = (chartAt H3 x.val).symm (liftHalf z) := by
  simp only [boundaryInverse,dite_eq_left hz]

@[simp] lemma boundaryChart_source (x : Boundary M) :
    (boundaryChart x).source = Subtype.val ⁻¹' (chartAt H3 x.val).source := rfl
@[simp] lemma boundaryChart_target (x : Boundary M) :
    (boundaryChart x).target = liftHalf ⁻¹' (chartAt H3 x.val).target := rfl
@[simp] lemma boundaryChart_apply (x y : Boundary M) :
    boundaryChart x y = dropPlane (I3 (chartAt H3 x.val y.val)) := rfl
lemma boundaryChart_symm_val (x : Boundary M) {z : E2} (hz : z ∈ (boundaryChart x).target) :
    ((boundaryChart x).symm z).val = (chartAt H3 x.val).symm (liftHalf z) :=
  boundaryInverse_val x hz

end CKSBoundarySurface

end

end OAI
