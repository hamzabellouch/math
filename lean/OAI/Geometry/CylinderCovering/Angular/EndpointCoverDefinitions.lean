import OAI.Geometry.CylinderCovering.Angular.EndpointDefinitions
import OAI.Geometry.CylinderCovering.Angular.FamilyDefinitions

namespace OAI

noncomputable section
namespace CylinderCovering

def AngularEndpointStatement : Prop :=
  ∀ k : ℕ, 14000 ≤ k →
    ∃ C : Fin (2*(k^2+1)) → TriangularCovering.TriCylinder,
      TriangularCovering.AngularFamily.PrescribedFamily C (1/(k:ℝ))
        (fun j => AngularEndpoint.boundary (k^2) j)
        (fun j => AngularEndpoint.boundary (k^2) (j+1))
        (fun j => AngularEndpoint.alpha (k^2) j)
        (fun j => AngularEndpoint.beta (k^2) j)
        (fun j => AngularEndpoint.radius (1/(k:ℝ)) (1/1000) (k^2) j) ∧
      TriangularCovering.Covers C ∧
      |TriangularCovering.totalArea C/TriangularCovering.H -
        (1/2-(13/6000:ℝ)*(1/(k:ℝ))^2)| ≤ 14*(1/(k:ℝ))^4 ∧
      TriangularCovering.totalArea C < TriangularCovering.A_min/2 ∧
      TriangularCovering.relativeCost C < 1/2

end CylinderCovering

end

end OAI
