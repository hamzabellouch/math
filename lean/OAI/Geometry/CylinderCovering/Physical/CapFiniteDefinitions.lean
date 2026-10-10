import OAI.Geometry.CylinderCovering.Physical.FiniteDefinitions
import OAI.Geometry.CylinderCovering.Radial.FinitePairDefinitions

namespace OAI

open Set Filter
open scoped Topology InnerProductSpace
noncomputable section
namespace RadialPhysical
open CylinderCovering

def capChoice (square : Bool) (b eta beta : ℝ) : ℝ → ℝ :=
  if square then squareCap b eta beta else linearCap b eta beta

def physicalModelCap (centered square : Bool) (b eta beta : ℝ) : ℝ → ℝ :=
  if centered then fun s => 2 * capChoice square b eta beta s
  else capChoice square b eta beta

def physicalHalfReference (centered : Bool) (b : ℝ) : ℝ :=
  if centered then 2*b*height b else b*height b/2

structure PhysicalFamilyConclusion (centered : Bool) (b eta : ℝ) (T : ℝ → ℝ)
    (tagU tagL : (N : ℕ) → Fin N → ℝ)
    (C : (N : ℕ) → Fin (2*N) → TriangularCovering.TriCylinder) : Prop where
  local_properties : ∀ N, 0 < N → ∀ i : Fin N,
    (C N (RadialPairedSweep.upperIndex i)).axis = upperPhysicalAxis b eta (tagU N i) ∧
    (C N (RadialPairedSweep.lowerIndex i)).axis = lowerPhysicalAxis b eta (tagL N i) ∧
    upperPhysicalBase centered b eta T N (tagU N) i ⊆
      (C N (RadialPairedSweep.upperIndex i)).base ∧
    lowerPhysicalBase centered b eta T N (tagL N) i ⊆
      (C N (RadialPairedSweep.lowerIndex i)).base ∧
    physicalBaseProperties (upperPhysicalAxis b eta (tagU N i))
      (upperPhysicalBase centered b eta T N (tagU N) i) ∧
    physicalBaseProperties (lowerPhysicalAxis b eta (tagL N i))
      (lowerPhysicalBase centered b eta T N (tagL N) i)
  covers_body : ∀ N, 0 < N → ∀ z ∈ modelBody centered b,
    ∃ i : Fin (2*N), z ∈ (C N i).carrier
  covers_sweeps : ∀ N, 0 < N →
    ∀ z ∈ upperSweepOn centered b eta T (Icc (-b) b) ∪
      lowerSweepOn centered b eta T (Icc (-b) b),
      ∃ i : Fin (2*N), z ∈ (C N i).carrier
  actual_covers_body : ∀ N, 0 < N → ∀ z ∈ modelBody centered b,
    (∃ i : Fin N, z ∈ RadialSweep.cylinder (upperPhysicalAxis b eta (tagU N i))
      (upperPhysicalBase centered b eta T N (tagU N) i)) ∨
    (∃ i : Fin N, z ∈ RadialSweep.cylinder (lowerPhysicalAxis b eta (tagL N i))
      (lowerPhysicalBase centered b eta T N (tagL N) i))
  triangle_limit : Tendsto (fun N => TriangularCovering.totalArea (C N)) atTop
    (𝓝 (scaledCost b eta T))
  actual_bound : ∀ δ : ℝ, 0 < δ → ∀ᶠ N in atTop,
    physicalActualCost centered b eta T N (tagU N) (tagL N) ≤ scaledCost b eta T + δ
  actual_limsup : Filter.limsup
    (fun N => physicalActualCost centered b eta T N (tagU N) (tagL N)) atTop ≤
      scaledCost b eta T

def PhysicalCapFiniteStatement : Prop :=
  ∀ (centered square : Bool) (b beta : ℝ), 0 < b → 0 < beta → beta < 1/60 →
    ∀ᶠ eta : ℝ in 𝓝[>] (0 : ℝ),
      ∀ tagU tagL : (N : ℕ) → Fin N → ℝ,
        (∀ N, RadialRiemann.IsTagged (-b) b N (tagU N)) →
        (∀ N, RadialRiemann.IsTagged (-b) b N (tagL N)) →
        ∃ C : (N : ℕ) → Fin (2*N) → TriangularCovering.TriCylinder,
          PhysicalFamilyConclusion centered b eta (physicalModelCap centered square b eta beta) tagU tagL C ∧
          ∀ᶠ N in atTop, 0 < N ∧
            TriangularCovering.totalArea (C N) < physicalHalfReference centered b ∧
            physicalActualCost centered b eta (physicalModelCap centered square b eta beta) N
              (tagU N) (tagL N) < physicalHalfReference centered b

def PhysicalCapCoverageStatement : Prop :=
  ∀ (centered square : Bool) (b beta : ℝ), 0 < b → 0 < beta →
    ∀ᶠ eta : ℝ in 𝓝[>] (0 : ℝ),
      ∀ tagU tagL : (N : ℕ) → Fin N → ℝ,
        (∀ N, RadialRiemann.IsTagged (-b) b N (tagU N)) →
        (∀ N, RadialRiemann.IsTagged (-b) b N (tagL N)) →
        ∃ C : (N : ℕ) → Fin (2*N) → TriangularCovering.TriCylinder,
          PhysicalFamilyConclusion centered b eta (physicalModelCap centered square b eta beta)
            tagU tagL C

end RadialPhysical

end

end OAI
