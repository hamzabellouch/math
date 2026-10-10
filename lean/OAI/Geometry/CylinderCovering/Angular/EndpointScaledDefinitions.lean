import OAI.Geometry.CylinderCovering.Angular.EndpointCoverDefinitions
import OAI.Geometry.CylinderCovering.Convexity.SimilarityDefinitions

namespace OAI

noncomputable section
namespace CylinderCovering

def endpointScaledBody : Set TriangularCovering.Space :=
  (fun z => (1/TriangularCovering.H) • z) '' TriangularCovering.K

def AngularEndpointScaledStatement : Prop :=
  Similarity.minimumArea endpointScaledBody = TriangularCovering.H/2 ∧
  ∀ k : ℕ, 14000 ≤ k →
    ∃ C D : Fin (2*(k^2+1)) → TriangularCovering.TriCylinder,
      TriangularCovering.AngularFamily.PrescribedFamily C (1/(k:ℝ))
        (fun j => AngularEndpoint.boundary (k^2) j)
        (fun j => AngularEndpoint.boundary (k^2) (j+1))
        (fun j => AngularEndpoint.alpha (k^2) j)
        (fun j => AngularEndpoint.beta (k^2) j)
        (fun j => AngularEndpoint.radius (1/(k:ℝ)) (1/1000) (k^2) j) ∧
      (∀ i, (D i).axis = (C i).axis ∧
        (D i).base = (fun z => (1/TriangularCovering.H) • z) '' (C i).base) ∧
      (∀ z ∈ endpointScaledBody, ∃ i, z ∈ (D i).carrier) ∧
      |TriangularCovering.totalArea D - (2/TriangularCovering.H)*
          (1/4-(13/12000:ℝ)*(1/(k:ℝ))^2)| ≤
        7*TriangularCovering.H*(1/(k:ℝ))^4 ∧
      TriangularCovering.totalArea D < Similarity.minimumArea endpointScaledBody/2 ∧
      (∑ i, TriangularCovering.area (D i).base /
        Similarity.shadowArea endpointScaledBody (D i).axis) < 1/2

end CylinderCovering

end

end OAI
