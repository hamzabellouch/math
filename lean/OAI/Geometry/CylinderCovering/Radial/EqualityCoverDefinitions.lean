import OAI.Geometry.CylinderCovering.Convexity.GlobalDefinitions
import OAI.Geometry.CylinderCovering.Radial.PairedSweepDefinitions

namespace OAI

noncomputable section
namespace CylinderCovering.RadialEqualityCover
open Set
open RadialPairedSweep

def firstAxis : Space := point 1 0 0
def secondAxis : Space := point 0 1 0

def firstBase : Set Space :=
  {z | ∃ y t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ |y| ≤ 1 - t ∧
    z = point 0 y (Real.sqrt 2 * t)}

def secondBase : Set Space :=
  (fun z : Space => point (z 1) (z 0) (-z 2)) '' firstBase

def Statement : Prop :=
  ∃ C : Fin 2 → TriangularCovering.TriCylinder,
    (C 0).axis = firstAxis ∧ (C 1).axis = secondAxis ∧
    (C 0).base = firstBase ∧ (C 1).base = secondBase ∧
    triangularCovers (tetrahedron (Real.sqrt 2)) C ∧
    (∀ i, TriangularCovering.area (C i).base = Real.sqrt 2) ∧
    TriangularCovering.totalArea C = 2 * Real.sqrt 2 ∧
    TriangularCovering.totalArea C =
      minimumShadowArea (tetrahedron (Real.sqrt 2)) / 2 ∧
    (∀ i, shadowArea (tetrahedron (Real.sqrt 2)) (C i).axis = 4 * Real.sqrt 2) ∧
    triangularRelativeCost (tetrahedron (Real.sqrt 2)) C = 1 / 2

end CylinderCovering.RadialEqualityCover

end

end OAI
