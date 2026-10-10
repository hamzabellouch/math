import OAI.Geometry.Relativity.CKS.SchwarzschildCharges
import OAI.Geometry.Relativity.CKS.SchwarzschildOrientability
import OAI.Geometry.Relativity.CKS.SchwarzschildCompleteness
import OAI.Geometry.Relativity.CKS.SchwarzschildVacuum
import OAI.Geometry.Relativity.CKS.SchwarzschildEqualityDefinitions
import OAI.Geometry.Relativity.CKS.SchwarzschildSpacetimeRegular
import OAI.Geometry.Relativity.CKS.SchwarzschildHorizon

namespace OAI

noncomputable section
open Set Filter Manifold Bundle CKSSpatialManifold CKSMetricGluing CKSLorentz
open scoped ContDiff Topology InnerProductSpace
namespace CKSSchwarzschild
open CKSBoundarySurface

lemma horizon_regular_graph {m : ℝ} (hm : 0 < m) : HorizonRegularGraph m where
  ambient_smooth := fun _ hx => advancedMetric_smoothAt m hx
  ambient_symmetric := advancedMetric_symm m
  ambient_nondegenerate := fun _ hx => advancedMetric_nondegenerate m hx
  graph_smooth_across := fun _ hx => advancedGraph_smooth hm hx
  graph_injective := advancedGraph_injective m
  graph_derivative := fun _ hx => advancedGraph_derivative hm hx
  horizon_time := advancedTime_horizon m
  horizon_slope := advancedSlope_horizon hm
  induced_metric := fun _ hx => graph_induced_metric hm hx
  normal_unit := fun _ hx => futureNormal_unit hm hx
  normal_orthogonal := fun _ hx => futureNormal_orthogonal hm hx
  future_facing := fun _ hx => futureNormal_future hm hx
  induced_second_form := fun _ hx => graph_induced_second_form hm hx

lemma source_boundary_nonempty : (I3.boundary Exterior).Nonempty := by
  let n : Sphere := ⟨EuclideanSpace.single 0 1,by simp⟩
  exact ⟨(boundarySphere.symm n).val,(boundarySphere.symm n).property⟩
lemma source_boundary_connected : ConnectedSpace (Boundary Exterior) := by
  let : ConnectedSpace Sphere := isConnected_iff_connectedSpace.mp
    (isConnected_sphere (by rw [← Module.finrank_eq_rank]; norm_num : 1 < Module.rank ℝ E3) (0 : E3) (by norm_num : (0 : ℝ) ≤ 1))
  exact boundarySphere.symm.connectedSpace_iff.mp inferInstance
lemma source_boundary_theta {m : ℝ} (hm : 0 < m) (p : Exterior) (hp : p ∈ I3.boundary Exterior) :
    sphereThetaPlus m (position m p) = 0 := by
  apply horizon_expansion hm
  rw [norm_position hm]
  have hh := (boundary_iff p).mp hp
  change 2*m+p.1.val = 2*m
  rw [hh,add_zero]

theorem schwarzschild_equality_example {m : ℝ} (hm : 0 < m) :
    SchwarzschildEqualityExample m hm where
  connected := inferInstance
  orientable := source_orientable
  boundary_nonempty := source_boundary_nonempty
  boundary_compact := boundary_compact
  boundary_connected := source_boundary_connected
  smooth_tensor := tensorInner_smooth hm
  symmetric_tensor := tensorInner_symm m
  complete := source_complete hm
  dec := physical_DEC hm
  exterior_CKS := ⟨cksData hm⟩
  bondi := bondi_charge hm
  timelike := by rw [bondi_charge hm]; simpa using hm
  horizon_regular := horizon_regular_graph hm
  boundary_normal_unit := fun _ hx => radialNormal_unit hm hx
  boundary_normal_orthogonal := fun _ _ hx => radialNormal_orthogonal m hx
  boundary_normal_points_into_end := fun _ hx => radialNormal_points_out hm hx
  boundary_theta_plus := source_boundary_theta hm
  full_cut_area := source_minimum_area hm
  positive_area := by rw [source_minimum_area hm]; positivity
  equality := numerical_equality hm
end CKSSchwarzschild

end

end OAI
