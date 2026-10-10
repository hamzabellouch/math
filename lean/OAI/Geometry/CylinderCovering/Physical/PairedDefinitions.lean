import OAI.Geometry.CylinderCovering.Physical.CostDefinitions
import OAI.Geometry.CylinderCovering.Convexity.SimilarityDefinitions

namespace OAI

noncomputable section
namespace CylinderCovering.UnitEdgeFootprints

def linearReflection (z : Space) : Space := !₂[-z 1, z 0, -z 2]

def reflection (z : Space) : Space := !₂[-z 1, z 0, height - z 2]

def secondRepresentedPoint (η s ρ y : ℝ) : Space :=
  !₂[s * ρ - η * y * (1 / 4 + s ^ 2), y, height * (1 - ρ + 2 * η * y * s)]

def secondSweep (η : ℝ) : Set Space :=
  {z | ∃ s ∈ Set.Icc (-1 / 2 : ℝ) (1 / 2), ∃ ρ ∈ Set.Icc (0 : ℝ) (sourceCap η s),
    ∃ y : ℝ, |y| ≤ 1 / 2 ∧ z = secondRepresentedPoint η s ρ y}

def secondAxis (η m : ℝ) : Space := linearReflection (axis η m)

def secondBase (η d M m : ℝ) : Set Space :=
  TriangularCovering.projection (secondAxis η m) '' (reflection '' foot η d M m)

def PairedFamilyStatement : Prop :=
  ∀ η : ℝ, 0 < η →
    ∃ C₁ C₂ : (N : ℕ) → Fin N → TriangularCovering.TriCylinder,
      (∀ N (i : Fin N),
        (C₁ N i).axis = axis η (midpoint N i) ∧
        (C₁ N i).base = base η (mesh N) (maximumCap (sourceCap η) N i) (midpoint N i) ∧
        (C₂ N i).axis = secondAxis η (midpoint N i) ∧
        (C₂ N i).base = secondBase η (mesh N) (maximumCap (sourceCap η) N i) (midpoint N i) ∧
        TriangularCovering.area (C₁ N i).base =
          areaFormula η (mesh N) (maximumCap (sourceCap η) N i) (midpoint N i) ∧
        TriangularCovering.area (C₂ N i).base =
          areaFormula η (mesh N) (maximumCap (sourceCap η) N i) (midpoint N i)) ∧
      (∀ N, 0 < N → ∀ z ∈ sweep η (sourceCap η) ∪ secondSweep η,
        ∃ i : Fin N, z ∈ (C₁ N i).carrier ∨ z ∈ (C₂ N i).carrier) ∧
      Filter.Tendsto (fun N => TriangularCovering.totalArea (C₁ N) +
        TriangularCovering.totalArea (C₂ N)) Filter.atTop
        (nhds (2 * limitingArea η (sourceCap η)))

def tetrahedron : Set Space :=
  {z | ∃ t ∈ Set.Icc (0 : ℝ) 1, z 2 = height * t ∧
    |z 0| ≤ (1 - t) / 2 ∧ |z 1| ≤ t / 2}

def CoverageStatement : Prop :=
  ∃ δ : ℝ, 0 < δ ∧ ∀ η : ℝ, 0 < η → η < δ →
    tetrahedron ⊆ sweep η (sourceCap η) ∪ secondSweep η

def FiniteStrictStatement : Prop :=
  ∃ δ : ℝ, 0 < δ ∧ ∀ η : ℝ, 0 < η → η < δ →
    ∃ N : ℕ, 0 < N ∧ ∃ C₁ C₂ : Fin N → TriangularCovering.TriCylinder,
      (∀ i, (C₁ i).axis = axis η (midpoint N i) ∧
        (C₁ i).base = base η (mesh N) (maximumCap (sourceCap η) N i) (midpoint N i) ∧
        (C₂ i).axis = secondAxis η (midpoint N i) ∧
        (C₂ i).base = secondBase η (mesh N) (maximumCap (sourceCap η) N i) (midpoint N i)) ∧
      (∀ z ∈ tetrahedron, ∃ i : Fin N, z ∈ (C₁ i).carrier ∨ z ∈ (C₂ i).carrier) ∧
      TriangularCovering.totalArea C₁ + TriangularCovering.totalArea C₂ < height / 4

def FullStatement : Prop :=
  LocalRealizationStatement ∧ FamilyRealizationStatement ∧ PairedFamilyStatement ∧
    SourceCostStatement ∧ CoverageStatement ∧ FiniteStrictStatement ∧
      Similarity.minimumArea tetrahedron = height / 2

end CylinderCovering.UnitEdgeFootprints

end

end OAI
