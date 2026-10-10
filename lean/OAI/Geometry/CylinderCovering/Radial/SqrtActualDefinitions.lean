import OAI.Geometry.CylinderCovering.Radial.SqrtRealizationDefinitions
import OAI.Geometry.CylinderCovering.Radial.PairedActualDefinitions
import OAI.Geometry.CylinderCovering.Radial.TetraGeometryDefinitions

namespace OAI

noncomputable section
open Set Filter
open scoped Topology
namespace CylinderCovering.RadialPairedSweep

def actualRelativeCost (ε : ℝ) (R : ℝ → ℝ) (N : ℕ)
    (tagU tagL : Fin N → ℝ) : ℝ :=
  (∑ i : Fin N, TriangularCovering.area
      (upperActualBase (Real.sqrt 2) ε R N tagU i) /
      shadowArea (tetrahedron (Real.sqrt 2)) (upperAxis (Real.sqrt 2) ε (tagU i))) +
  (∑ i : Fin N, TriangularCovering.area
      (lowerActualBase (Real.sqrt 2) ε R N tagL i) /
      shadowArea (tetrahedron (Real.sqrt 2)) (lowerAxis (Real.sqrt 2) ε (tagL i)))

end CylinderCovering.RadialPairedSweep
namespace CylinderCovering.RadialSqrtCap
open RadialPairedSweep

def ActualFamilyConclusion (β ε : ℝ) (tagU tagL : (N : ℕ) → Fin N → ℝ) : Prop :=
  (∀ N, 0 < N →
    (∀ i : Fin N,
      ActualBaseProperties (upperAxis (Real.sqrt 2) ε (tagU N i))
        (upperActualBase (Real.sqrt 2) ε (cap β ε) N (tagU N) i) ∧
      ActualBaseProperties (lowerAxis (Real.sqrt 2) ε (tagL N i))
        (lowerActualBase (Real.sqrt 2) ε (cap β ε) N (tagL N) i)) ∧
    (∀ z ∈ tetrahedron (Real.sqrt 2),
      (∃ i : Fin N, z ∈ RadialSweep.cylinder (upperAxis (Real.sqrt 2) ε (tagU N i))
        (upperActualBase (Real.sqrt 2) ε (cap β ε) N (tagU N) i)) ∨
      (∃ i : Fin N, z ∈ RadialSweep.cylinder (lowerAxis (Real.sqrt 2) ε (tagL N i))
        (lowerActualBase (Real.sqrt 2) ε (cap β ε) N (tagL N) i)))) ∧
  (∀ η : ℝ, 0 < η → ∀ᶠ N in atTop,
    pairedActualCost (Real.sqrt 2) ε (cap β ε) N (tagU N) (tagL N) ≤
      2 * Real.sqrt 2 * cost β ε + η) ∧
  Filter.limsup (fun N => pairedActualCost (Real.sqrt 2) ε (cap β ε) N
    (tagU N) (tagL N)) atTop ≤ 2 * Real.sqrt 2 * cost β ε

def ActualFullStatement : Prop :=
  (∀ β : ℝ, 0 < β → ∃ δ : ℝ, 0 < δ ∧
    ∀ ε : ℝ, 0 < ε → ε < δ →
      ∀ tagU tagL : (N : ℕ) → Fin N → ℝ,
        (∀ N, RadialRiemann.IsTagged (-1) 1 N (tagU N)) →
        (∀ N, RadialRiemann.IsTagged (-1) 1 N (tagL N)) →
        ActualFamilyConclusion β ε tagU tagL) ∧
  (∀ β : ℝ, 0 < β → β < 1 / 60 → ∃ δ : ℝ, 0 < δ ∧
    ∀ ε : ℝ, 0 < ε → ε < δ →
      ∀ tagU tagL : (N : ℕ) → Fin N → ℝ,
        (∀ N, RadialRiemann.IsTagged (-1) 1 N (tagU N)) →
        (∀ N, RadialRiemann.IsTagged (-1) 1 N (tagL N)) →
        ActualFamilyConclusion β ε tagU tagL ∧
        ∀ᶠ N in atTop, 0 < N ∧
          pairedActualCost (Real.sqrt 2) ε (cap β ε) N (tagU N) (tagL N) <
            minimumShadowArea (tetrahedron (Real.sqrt 2)) / 2 ∧
          actualRelativeCost ε (cap β ε) N (tagU N) (tagL N) < 1 / 2)

def CompleteStatement : Prop :=
  FullStatement ∧ ActualFullStatement ∧
    ReferenceAreaStatement ∧ HalfCostStatement

end CylinderCovering.RadialSqrtCap

end

end OAI
