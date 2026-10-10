import OAI.Geometry.CylinderCovering.Physical.FiniteDefinitions
import OAI.Geometry.CylinderCovering.Convexity.GlobalDefinitions

namespace OAI

open Set
noncomputable section
namespace RadialPhysical.PhysicalMinimum
open CylinderCovering

def actualRelativeCost (centered : Bool) (b eta : ℝ) (T : ℝ → ℝ)
    (N : ℕ) (tagU tagL : Fin N → ℝ) : ℝ :=
  (∑ i, TriangularCovering.area (upperPhysicalBase centered b eta T N tagU i) /
    CylinderCovering.shadowArea (modelBody centered b) (upperPhysicalAxis b eta (tagU i))) +
  (∑ i, TriangularCovering.area (lowerPhysicalBase centered b eta T N tagL i) /
    CylinderCovering.shadowArea (modelBody centered b) (lowerPhysicalAxis b eta (tagL i)))

def Statement : Prop :=
  (∀ (centered : Bool) (b : ℝ), 0 < b →
    minimumShadowArea (modelBody centered b) = (if centered then 4 else 1)*b*height b ∧
    (∃ u : Space, ‖u‖ = 1 ∧
      CylinderCovering.shadowArea (modelBody centered b) u =
        minimumShadowArea (modelBody centered b)) ∧
    (∀ u : Space, ‖u‖ = 1 →
      (if centered then 4 else 1)*b*height b ≤
        CylinderCovering.shadowArea (modelBody centered b) u) ∧
    (∀ (n : ℕ) (C : Fin n → TriangularCovering.TriCylinder),
      TriangularCovering.totalArea C < ((if centered then 4 else 1)*b*height b)/2 →
      TriangularCovering.totalArea C < minimumShadowArea (modelBody centered b)/2 ∧
        triangularRelativeCost (modelBody centered b) C < 1/2)) ∧
  minimumShadowArea {z : Space | ∃ p q t : ℝ,
    |p| ≤ 1+t ∧ |q| ≤ 1-t ∧ z = nonorthPoint p q t} = 2*Real.sqrt 2 ∧
  (∀ (centered : Bool) (b : ℝ), 0 < b → ∀ (eta : ℝ) (T : ℝ → ℝ)
    (N : ℕ) (tagU tagL : Fin N → ℝ),
    physicalActualCost centered b eta T N tagU tagL <
      ((if centered then 4 else 1)*b*height b)/2 →
    physicalActualCost centered b eta T N tagU tagL <
      minimumShadowArea (modelBody centered b)/2 ∧
    actualRelativeCost centered b eta T N tagU tagL < 1/2)

end RadialPhysical.PhysicalMinimum

end

end OAI
