import OAI.Geometry.CylinderCovering.Physical.CapFiniteDefinitions
import OAI.Geometry.CylinderCovering.Convexity.GlobalDefinitions

namespace OAI

open Set Filter
open scoped Topology
noncomputable section
namespace RadialPhysical
open CylinderCovering

def physicalActualRelativeCost (centered : Bool) (b eta : ℝ) (T : ℝ → ℝ)
    (N : ℕ) (tagU tagL : Fin N → ℝ) : ℝ :=
  (∑ i : Fin N, TriangularCovering.area (upperPhysicalBase centered b eta T N tagU i) /
    shadowArea (modelBody centered b) (upperPhysicalAxis b eta (tagU i))) +
  (∑ i : Fin N, TriangularCovering.area (lowerPhysicalBase centered b eta T N tagL i) /
    shadowArea (modelBody centered b) (lowerPhysicalAxis b eta (tagL i)))

def PhysicalBothHalfBounds (centered : Bool) (b eta : ℝ) (T : ℝ → ℝ)
    (N : ℕ) (tagU tagL : Fin N → ℝ)
    (C : Fin (2*N) → TriangularCovering.TriCylinder) : Prop :=
  TriangularCovering.totalArea C < minimumShadowArea (modelBody centered b)/2 ∧
  triangularRelativeCost (modelBody centered b) C < 1/2 ∧
  physicalActualCost centered b eta T N tagU tagL < minimumShadowArea (modelBody centered b)/2 ∧
  physicalActualRelativeCost centered b eta T N tagU tagL < 1/2

def PhysicalCapNormalizedStatement : Prop :=
  ∀ (centered square : Bool) (b beta : ℝ), 0 < b → 0 < beta → beta < 1/60 →
    ∀ᶠ eta : ℝ in 𝓝[>] (0 : ℝ),
      ∀ tagU tagL : (N : ℕ) → Fin N → ℝ,
        (∀ N, RadialRiemann.IsTagged (-b) b N (tagU N)) →
        (∀ N, RadialRiemann.IsTagged (-b) b N (tagL N)) →
        ∃ C : (N : ℕ) → Fin (2*N) → TriangularCovering.TriCylinder,
          PhysicalFamilyConclusion centered b eta (physicalModelCap centered square b eta beta)
            tagU tagL C ∧
          ∀ᶠ N in atTop, 0 < N ∧
            PhysicalBothHalfBounds centered b eta (physicalModelCap centered square b eta beta)
              N (tagU N) (tagL N) (C N)

end RadialPhysical

end

end OAI
