import OAI.Geometry.CylinderCovering.Convexity.GlobalDefinitions
import OAI.Geometry.CylinderCovering.Rational.RealizationDefinitions

namespace OAI

noncomputable section
open Set

namespace SlopeRational.EqualityCover

def labelTriangle : Set RuledApproximation.Plane :=
  {p | 0 ≤ p 1 ∧ p 1 ≤ (1 / 2 : ℝ) ∧ 2 * |p 0| ≤ 1 / 2 - p 1}

def firstBase : Set Space :=
  (fun p : RuledApproximation.Plane =>
    RuledApproximation.vec3 0 (p 0) (physicalScale * p 1)) '' labelTriangle

def secondBase : Set Space := reflection '' firstBase

def firstAxis : Space := RuledApproximation.vec3 1 0 0

def secondAxis : Space := RuledApproximation.vec3 0 1 0

def Statement : Prop :=
  ∃ C : Fin 2 → TriangularCovering.TriCylinder,
    (C 0).axis = firstAxis ∧ (C 1).axis = secondAxis ∧
    (C 0).base = firstBase ∧ (C 1).base = secondBase ∧
    CylinderCovering.triangularCovers referenceTetrahedron C ∧
    (∀ i, TriangularCovering.area (C i).base = physicalScale / 8) ∧
    TriangularCovering.totalArea C = physicalScale / 4 ∧
    TriangularCovering.totalArea C =
      CylinderCovering.minimumShadowArea referenceTetrahedron / 2 ∧
    (∀ i, CylinderCovering.shadowArea referenceTetrahedron (C i).axis = physicalScale / 2) ∧
    CylinderCovering.triangularRelativeCost referenceTetrahedron C = 1 / 2

end SlopeRational.EqualityCover

end

end OAI
