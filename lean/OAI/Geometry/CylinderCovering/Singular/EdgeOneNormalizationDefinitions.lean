import OAI.Geometry.CylinderCovering.Singular.EdgeOneCoverDefinitions
import OAI.Geometry.CylinderCovering.Rational.RealizationDefinitions
import OAI.Geometry.CylinderCovering.Convexity.GlobalDefinitions

namespace OAI

noncomputable section
open Set

namespace CylinderCovering.SingularEdgeOneCover
open RuledApproximation

def NormalizationStatement : Prop :=
  tetrahedron =
    (fun z : Space => z + vec3 0 0 (height / 2)) '' SlopeRational.referenceTetrahedron ∧
  minimumShadowArea tetrahedron = height / 2 ∧
  ∀ (n m : ℕ) (C : Fin n → Cylinder) (D : Fin m → Cylinder) (B₁ B₂ : Cylinder),
    familyArea C + familyArea D + B₁.area + B₂.area < height / 4 →
    familyArea C + familyArea D + B₁.area + B₂.area <
      minimumShadowArea tetrahedron / 2 ∧
    relativeCost tetrahedron C + relativeCost tetrahedron D +
      B₁.area / shadowArea tetrahedron B₁.axis +
      B₂.area / shadowArea tetrahedron B₂.axis < 1 / 2

end CylinderCovering.SingularEdgeOneCover

end

end OAI
