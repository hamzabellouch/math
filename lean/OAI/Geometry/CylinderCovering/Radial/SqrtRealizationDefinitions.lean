import OAI.Geometry.CylinderCovering.Radial.SqrtCapDefinitions
import OAI.Geometry.CylinderCovering.Radial.FinitePairDefinitions

namespace OAI

noncomputable section
namespace CylinderCovering.RadialSqrtCap
open Set Filter
open scoped Topology

def FamilyConclusion (β ε : ℝ)
    (tagU tagL : (N : ℕ) → Fin N → ℝ)
    (C : (N : ℕ) → Fin (2 * N) → TriangularCovering.TriCylinder) : Prop :=
  (∀ N, 0 < N →
    (∀ i : Fin N,
      (C N (RadialPairedSweep.upperIndex i)).axis =
        RadialPairedSweep.upperAxis (Real.sqrt 2) ε (tagU N i) ∧
      (C N (RadialPairedSweep.lowerIndex i)).axis =
        RadialPairedSweep.lowerAxis (Real.sqrt 2) ε (tagL N i)) ∧
    (∀ z ∈ RadialPairedSweep.tetrahedron (Real.sqrt 2),
      ∃ i : Fin (2 * N), z ∈ (C N i).carrier) ∧
    (∀ z ∈ RadialPairedSweep.upperSweep (Real.sqrt 2) ε (cap β ε) ∪
      RadialPairedSweep.lowerSweep (Real.sqrt 2) ε (cap β ε),
      ∃ i : Fin (2 * N), z ∈ (C N i).carrier)) ∧
  Tendsto (fun N => TriangularCovering.totalArea (C N)) atTop
    (𝓝 (2 * Real.sqrt 2 * cost β ε))

def FullStatement : Prop :=
  (∀ β ε : ℝ, 0 ≤ β → |ε| ≤ 1 →
    |cost β ε - (1 + (2 * β - 1 / 30) * ε ^ 2)| ≤ (14 + 10 * β) * ε ^ 4) ∧
  (∀ β : ℝ, 0 < β → ∃ δ : ℝ, 0 < δ ∧
    ∀ ε : ℝ, 0 < ε → ε < δ →
      (RadialPairedSweep.tetrahedron (Real.sqrt 2) ⊆
        RadialPairedSweep.upperSweep (Real.sqrt 2) ε (cap β ε) ∪
        RadialPairedSweep.lowerSweep (Real.sqrt 2) ε (cap β ε)) ∧
      ∀ tagU tagL : (N : ℕ) → Fin N → ℝ,
        (∀ N, RadialRiemann.IsTagged (-1) 1 N (tagU N)) →
        (∀ N, RadialRiemann.IsTagged (-1) 1 N (tagL N)) →
        ∃ C : (N : ℕ) → Fin (2 * N) → TriangularCovering.TriCylinder,
          FamilyConclusion β ε tagU tagL C) ∧
  (∀ β : ℝ, 0 < β → β < 1 / 60 → ∃ δ : ℝ, 0 < δ ∧
    ∀ ε : ℝ, 0 < ε → ε < δ → cost β ε < 1 ∧
      ∀ tagU tagL : (N : ℕ) → Fin N → ℝ,
        (∀ N, RadialRiemann.IsTagged (-1) 1 N (tagU N)) →
        (∀ N, RadialRiemann.IsTagged (-1) 1 N (tagL N)) →
        ∃ C : (N : ℕ) → Fin (2 * N) → TriangularCovering.TriCylinder,
          FamilyConclusion β ε tagU tagL C ∧
          ∀ᶠ N in atTop, 0 < N ∧
            TriangularCovering.totalArea (C N) < 2 * Real.sqrt 2)

end CylinderCovering.RadialSqrtCap

end

end OAI
