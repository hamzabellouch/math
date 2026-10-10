import OAI.Geometry.CylinderCovering.Radial.PairedSweepDefinitions

namespace OAI

noncomputable section
open Set Filter
open scoped Topology
namespace CylinderCovering.RadialCapVariants

abbrev Space := TriangularCovering.Space

def CoverLimit (ε : ℝ) (R : ℝ → ℝ) : Prop :=
  ∀ tagU tagL : (N : ℕ) → Fin N → ℝ,
    (∀ N, RadialRiemann.IsTagged (-1) 1 N (tagU N)) →
    (∀ N, RadialRiemann.IsTagged (-1) 1 N (tagL N)) →
    ∃ U L : (N : ℕ) → Fin N → TriangularCovering.TriCylinder,
      (∀ N, 0 < N →
        (∀ i, (U N i).axis = RadialPairedSweep.upperAxis (Real.sqrt 2) ε (tagU N i) ∧
          (L N i).axis = RadialPairedSweep.lowerAxis (Real.sqrt 2) ε (tagL N i)) ∧
        (∀ z ∈ RadialPairedSweep.upperSweep (Real.sqrt 2) ε R,
          ∃ i : Fin N, z ∈ (U N i).carrier) ∧
        (∀ z ∈ RadialPairedSweep.lowerSweep (Real.sqrt 2) ε R,
          ∃ i : Fin N, z ∈ (L N i).carrier) ∧
        (∀ z ∈ RadialPairedSweep.tetrahedron (Real.sqrt 2),
          (∃ i : Fin N, z ∈ (U N i).carrier) ∨ (∃ i : Fin N, z ∈ (L N i).carrier))) ∧
      Tendsto (fun N => TriangularCovering.totalArea (U N) +
        TriangularCovering.totalArea (L N)) atTop (𝓝 (2 * Real.sqrt 2 * RadialCaps.Q R ε))

def FiniteSaving (ε : ℝ) : Prop :=
  ∀ tagU tagL : (N : ℕ) → Fin N → ℝ,
    (∀ N, RadialRiemann.IsTagged (-1) 1 N (tagU N)) →
    (∀ N, RadialRiemann.IsTagged (-1) 1 N (tagL N)) →
    ∃ N : ℕ, 0 < N ∧ ∃ U L : Fin N → TriangularCovering.TriCylinder,
      (∀ i, (U i).axis = RadialPairedSweep.upperAxis (Real.sqrt 2) ε (tagU N i) ∧
        (L i).axis = RadialPairedSweep.lowerAxis (Real.sqrt 2) ε (tagL N i)) ∧
      (∀ z ∈ RadialPairedSweep.tetrahedron (Real.sqrt 2),
        (∃ i : Fin N, z ∈ (U i).carrier) ∨ (∃ i : Fin N, z ∈ (L i).carrier)) ∧
      TriangularCovering.totalArea U + TriangularCovering.totalArea L < 2 * Real.sqrt 2

def SweepsCover (ε : ℝ) (R : ℝ → ℝ) : Prop :=
  RadialPairedSweep.tetrahedron (Real.sqrt 2) ⊆
    RadialPairedSweep.upperSweep (Real.sqrt 2) ε R ∪
      RadialPairedSweep.lowerSweep (Real.sqrt 2) ε R

def LCFStatement : Prop :=
  (∀ β : ℝ, 0 < β →
    (∀ᶠ ε : ℝ in 𝓝[>] 0,
      SweepsCover ε (RadialCaps.linearCap β ε) ∧ CoverLimit ε (RadialCaps.linearCap β ε)) ∧
    ((fun ε => RadialCaps.Q (RadialCaps.linearCap β ε) ε -
      (1 + (2 * β - 1 / 30) * ε ^ 2)) =O[𝓝[>] (0 : ℝ)] (fun ε => ε ^ 4)) ∧
    (β < 1 / 60 → ∀ᶠ ε : ℝ in 𝓝[>] 0,
      RadialCaps.Q (RadialCaps.linearCap β ε) ε < 1 ∧ FiniteSaving ε)) ∧
  (∀ c : ℝ, 9 / 2 ≤ c →
    (∀ ε : ℝ, 0 < ε →
      SweepsCover ε (RadialCaps.cubicCap c ε) ∧ CoverLimit ε (RadialCaps.cubicCap c ε)) ∧
    ((fun ε => RadialCaps.Q (RadialCaps.cubicCap c ε) ε -
      (1 - ε ^ 2 / 30 + 2 * c * ε ^ 3)) =O[𝓝[>] (0 : ℝ)] (fun ε => ε ^ 4)) ∧
    (∀ᶠ ε : ℝ in 𝓝[>] 0,
      RadialCaps.Q (RadialCaps.cubicCap c ε) ε < 1 ∧ FiniteSaving ε)) ∧
  (∀ c : ℝ, 0 < c →
    (∀ᶠ ε : ℝ in 𝓝[>] 0,
      SweepsCover ε (RadialCaps.fractionalCap c ε) ∧ CoverLimit ε (RadialCaps.fractionalCap c ε)) ∧
    ((fun ε => RadialCaps.Q (RadialCaps.fractionalCap c ε) ε -
      (1 - ε ^ 2 / 30 + 2 * c * ε ^ (5 / 2 : ℝ))) =O[𝓝[>] (0 : ℝ)] (fun ε => ε ^ 4)) ∧
    (∀ᶠ ε : ℝ in 𝓝[>] 0,
      RadialCaps.Q (RadialCaps.fractionalCap c ε) ε < 1 ∧ FiniteSaving ε))

end CylinderCovering.RadialCapVariants

end

end OAI
