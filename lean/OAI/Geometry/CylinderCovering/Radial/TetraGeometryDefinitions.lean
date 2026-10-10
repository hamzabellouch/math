import OAI.Geometry.CylinderCovering.Convexity.GlobalDefinitions
import OAI.Geometry.CylinderCovering.Radial.PairedSweepDefinitions

namespace OAI

noncomputable section
namespace CylinderCovering.RadialPairedSweep

def ReferenceAreaStatement : Prop :=
  minimumShadowArea (tetrahedron (Real.sqrt 2)) = 4 * Real.sqrt 2 ∧
    ∀ u : Space, ‖u‖ = 1 →
      4 * Real.sqrt 2 ≤ shadowArea (tetrahedron (Real.sqrt 2)) u

def HalfCostStatement : Prop :=
  ∀ n : ℕ, ∀ C : Fin n → TriangularCovering.TriCylinder,
    TriangularCovering.totalArea C < 2 * Real.sqrt 2 →
    TriangularCovering.totalArea C < minimumShadowArea (tetrahedron (Real.sqrt 2)) / 2 ∧
    triangularRelativeCost (tetrahedron (Real.sqrt 2)) C < 1 / 2

end CylinderCovering.RadialPairedSweep

end

end OAI
