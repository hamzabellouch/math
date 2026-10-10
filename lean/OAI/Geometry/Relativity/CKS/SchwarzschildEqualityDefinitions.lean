import OAI.Geometry.Relativity.CKS.ComparatorDefinitions
import OAI.Geometry.Relativity.CKS.SchwarzschildCKS
import OAI.Geometry.Relativity.CKS.SchwarzschildBoundary
import OAI.Geometry.Relativity.CKS.SourceReplacementDefinitions
import OAI.Geometry.Relativity.CKS.SchwarzschildConnectionDefinitions
import OAI.Geometry.Relativity.CKS.SchwarzschildSpacetimeDefinitions

namespace OAI

noncomputable section
open Set Filter Manifold Bundle CKSSpatialManifold CKSMetricGluing CKSLorentz
open scoped ContDiff Topology InnerProductSpace
namespace CKSSchwarzschild
open CKSBoundarySurface
local instance schwarzschildEqualityCotangentTopology : TopologicalSpace (TotalSpace (E3 →L[ℝ] ℝ)
    (fun x : Exterior => TangentSpace I3 x →L[ℝ] ℝ)) := inferInstance

structure SchwarzschildEqualityExample (m : ℝ) (hm : 0 < m) : Prop where
  connected : ConnectedSpace Exterior
  orientable : CKSSourceExterior.Orientable (N := Exterior)
  boundary_nonempty : (I3.boundary Exterior).Nonempty
  boundary_compact : IsCompact (I3.boundary Exterior)
  boundary_connected : ConnectedSpace (Boundary Exterior)
  smooth_tensor : ContMDiff I3 (I3.prod 𝓘(ℝ,SpatialBilinear)) ∞
    (innerSection I3 (tensorInner m))
  symmetric_tensor : ∀ p v w, tensorInner m p v w = tensorInner m p w v
  complete : CKSReplacementCompleteness.IsComplete I3 (smoothMetric hm).toContinuousRiemannianMetric
  dec : PhysicalDEC I3 (smoothMetric hm).inner (tensorInner m)
  exterior_CKS : Nonempty (CKSSourceExterior.CKSData (smoothMetric hm) (tensorInner m))
  bondi : CKSLorentz.bondiCharge (cksData hm).massAspect = (m,0)
  timelike : ‖(CKSLorentz.bondiCharge (cksData hm).massAspect).2‖ <
    (CKSLorentz.bondiCharge (cksData hm).massAspect).1
  horizon_regular : HorizonRegularGraph m
  boundary_normal_unit : ∀ x : E3, 2*m ≤ ‖x‖ →
    cartMetric m x (radialNormal m x) (radialNormal m x) = 1
  boundary_normal_orthogonal : ∀ x a : E3, ⟪radialUnit x,a⟫_ℝ = 0 →
    cartMetric m x (radialNormal m x) a = 0
  boundary_normal_points_into_end : ∀ x : E3, 2*m ≤ ‖x‖ →
    0 < fderiv ℝ (fun y : E3 => ‖y‖) x (radialNormal m x)
  boundary_theta_plus : ∀ p ∈ I3.boundary Exterior, sphereThetaPlus m (position m p) = 0
  full_cut_area : CKSSourceExterior.minimumEnclosingArea (smoothMetric hm) = 16*Real.pi*m^2
  positive_area : 0 < CKSSourceExterior.minimumEnclosingArea (smoothMetric hm)
  equality : Real.sqrt ((CKSLorentz.bondiCharge (cksData hm).massAspect).1^2 -
    ‖(CKSLorentz.bondiCharge (cksData hm).massAspect).2‖^2) =
    Real.sqrt (CKSSourceExterior.minimumEnclosingArea (smoothMetric hm) / (16*Real.pi))
end CKSSchwarzschild

end

end OAI
