import OAI.Geometry.CylinderCovering.Convexity.GlobalDefinitions

namespace OAI

noncomputable section
namespace CylinderCovering

def RegularExplicitAngularStatement : Prop :=
  ∀ K : Set Space, IsRegularTetrahedron K →
    ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2000 →
      ∃ C : Fin (2 * TriangularCovering.n ε) → TriangularCovering.TriCylinder,
        triangularCovers K C ∧
        |TriangularCovering.totalArea C / minimumShadowArea K -
          (1 / 2 - (13 / 6000 : ℝ) * ε ^ 2)| ≤ 2 * ε ^ 4 ∧
        TriangularCovering.totalArea C < minimumShadowArea K / 2 ∧
        triangularRelativeCost K C < 1 / 2

end CylinderCovering

end

end OAI
