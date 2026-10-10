import OAI.Geometry.CylinderCovering.Radial.PairedSweepDefinitions

namespace OAI

noncomputable section
namespace CylinderCovering.HalfHeightCaps

def alpha (r : ℝ) : ℝ := (1 + r ^ 2) / 4
def beta (r : ℝ) : ℝ := r / 2
def F (r : ℝ) : ℝ := r ^ 2 * (1 + r ^ 2) / 16
def cubicCap (δ r : ℝ) : ℝ := 1 / 2 + δ ^ 2 * F r + 4 * δ ^ 3
def fractionalCap (δ r : ℝ) : ℝ := 1 / 2 + δ ^ 2 * F r + δ ^ (5 / 2 : ℝ)

def Covered (δ : ℝ) (R : ℝ → ℝ) : Prop :=
  ∀ X Y Z : ℝ, |X| ≤ 1 - Z → |Y| ≤ Z →
    (∃ r u : ℝ, |r| ≤ 1 ∧ 0 ≤ u ∧ u ≤ R r ∧
      Y = u * r + δ * X * alpha r ∧ Z = u + δ * X * beta r) ∨
    (∃ s v : ℝ, |s| ≤ 1 ∧ 0 ≤ v ∧ v ≤ R s ∧
      X = v * s - δ * Y * alpha s ∧ 1 - Z = v - δ * Y * beta s)

def CoverageStatement : Prop :=
  (∀ δ : ℝ, 0 < δ → Covered δ (cubicCap δ)) ∧
  (∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ → Covered δ (fractionalCap δ)) ∧
  (∀ δ r : ℝ, 2 * cubicCap δ r = RadialCaps.cubicCap 64 (δ / 2) r) ∧
  (∀ δ r : ℝ, 0 < δ → 2 * fractionalCap δ r =
    RadialCaps.fractionalCap (8 * Real.sqrt 2) (δ / 2) r)

def CompensationStatement : Prop :=
  ∀ δ X Y Z r s u v : ℝ,
    Y = u * r + δ * X * alpha r → Z = u + δ * X * beta r →
    X = v * s - δ * Y * alpha s → 1 - Z = v - δ * Y * beta s →
    (u - 1 / 2) * (1 - δ * X * r) + (v - 1 / 2) * (1 + δ * Y * s) =
      δ ^ 2 * (X ^ 2 * alpha r + Y ^ 2 * alpha s)

def physicalPoint (X Y Z : ℝ) : RadialPairedSweep.Space :=
  RadialPairedSweep.point (X / 2) (Y / 2) (Z / Real.sqrt 2)

def physicalTetrahedron : Set RadialPairedSweep.Space :=
  {z | ∃ X Y Z : ℝ, |X| ≤ 1 - Z ∧ |Y| ≤ Z ∧ z = physicalPoint X Y Z}

def firstPhysicalSweep (δ : ℝ) (R : ℝ → ℝ) : Set RadialPairedSweep.Space :=
  {z | ∃ r ∈ Set.Icc (-1 : ℝ) 1, ∃ u ∈ Set.Icc (0 : ℝ) (R r),
    ∃ X : ℝ, |X| ≤ 1 ∧ z = physicalPoint X (u * r + δ * X * alpha r)
      (u + δ * X * beta r)}

def secondPhysicalSweep (δ : ℝ) (R : ℝ → ℝ) : Set RadialPairedSweep.Space :=
  {z | ∃ s ∈ Set.Icc (-1 : ℝ) 1, ∃ v ∈ Set.Icc (0 : ℝ) (R s),
    ∃ Y : ℝ, |Y| ≤ 1 ∧ z = physicalPoint (v * s - δ * Y * alpha s) Y
      (1 - v + δ * Y * beta s)}

def PhysicalCoverageStatement : Prop :=
  (∀ δ : ℝ, 0 < δ → physicalTetrahedron ⊆
    firstPhysicalSweep δ (cubicCap δ) ∪ secondPhysicalSweep δ (cubicCap δ)) ∧
  (∀ δ : ℝ, 0 < δ → δ ≤ 1 → physicalTetrahedron ⊆
    firstPhysicalSweep δ (fractionalCap δ) ∪ secondPhysicalSweep δ (fractionalCap δ))

end CylinderCovering.HalfHeightCaps

end

end OAI
