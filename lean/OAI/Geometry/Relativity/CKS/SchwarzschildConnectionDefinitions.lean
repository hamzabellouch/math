import OAI.Geometry.Relativity.CKS.ComparatorDefinitions
import OAI.Geometry.Relativity.CKS.SchwarzschildMetricDefinitions
import OAI.Geometry.Relativity.CKS.InducedMetric

namespace OAI

noncomputable section
open Manifold Bundle Set Filter
open scoped ContDiff Topology InnerProductSpace
namespace CKSSchwarzschild
open CKSBoundarySurface

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
def radialNormal (m : ℝ) (x : E3) : E3 := lapse m ‖x‖ • radialUnit x
def tangentProjection (x a : E3) : E3 := a - ⟪radialUnit x,a⟫_ℝ • radialUnit x

def sphereMeanCurvature (m : ℝ) (x : E3) : ℝ :=
  ∑ i : Fin 3, covariantPair (cartMetric m) (radialNormal m) x
    (tangentProjection x (EuclideanSpace.single i 1))
    (tangentProjection x (EuclideanSpace.single i 1))
def sphereTensorTrace (m : ℝ) (x : E3) : ℝ :=
  ∑ i : Fin 3, cartTensor m x
    (tangentProjection x (EuclideanSpace.single i 1))
    (tangentProjection x (EuclideanSpace.single i 1))
def sphereThetaPlus (m : ℝ) (x : E3) : ℝ := sphereMeanCurvature m x + sphereTensorTrace m x
end CKSSchwarzschild

end

end OAI
