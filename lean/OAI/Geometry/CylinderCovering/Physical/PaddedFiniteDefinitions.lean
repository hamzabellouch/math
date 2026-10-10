import OAI.Geometry.CylinderCovering.Physical.CapNormalizedDefinitions

namespace OAI

open Set Filter
open scoped Topology
noncomputable section
namespace RadialPhysical
open CylinderCovering

def paddedNumerator (fractional : Bool) (b eta c s : ℝ) : ℝ :=
  1 + eta^2 * (s^4 + b^2*s^2)/2 +
    c * (if fractional then eta^(5/2 : ℝ) else eta^3)

def physicalPaddedCap (centered fractional : Bool) (b eta c : ℝ) : ℝ → ℝ :=
  if centered then paddedNumerator fractional b eta c
  else fun s => paddedNumerator fractional b eta c s / 2

def PaddedFiniteAt (centered fractional : Bool) (b eta c : ℝ) : Prop :=
  ∀ tagU tagL : (N : ℕ) → Fin N → ℝ,
    (∀ N, RadialRiemann.IsTagged (-b) b N (tagU N)) →
    (∀ N, RadialRiemann.IsTagged (-b) b N (tagL N)) →
    ∃ C : (N : ℕ) → Fin (2*N) → TriangularCovering.TriCylinder,
      PhysicalFamilyConclusion centered b eta
        (physicalPaddedCap centered fractional b eta c) tagU tagL C

def PaddedStrictFiniteAt (centered fractional : Bool) (b eta c : ℝ) : Prop :=
  ∀ tagU tagL : (N : ℕ) → Fin N → ℝ,
    (∀ N, RadialRiemann.IsTagged (-b) b N (tagU N)) →
    (∀ N, RadialRiemann.IsTagged (-b) b N (tagL N)) →
    ∃ C : (N : ℕ) → Fin (2*N) → TriangularCovering.TriCylinder,
      PhysicalFamilyConclusion centered b eta
        (physicalPaddedCap centered fractional b eta c) tagU tagL C ∧
      ∀ᶠ N in atTop, 0 < N ∧
        TriangularCovering.totalArea (C N) < physicalHalfReference centered b ∧
        physicalActualCost centered b eta
          (physicalPaddedCap centered fractional b eta c) N (tagU N) (tagL N) <
            physicalHalfReference centered b

def PaddedNormalizedFiniteAt (centered fractional : Bool) (b eta c : ℝ) : Prop :=
  ∀ tagU tagL : (N : ℕ) → Fin N → ℝ,
    (∀ N, RadialRiemann.IsTagged (-b) b N (tagU N)) →
    (∀ N, RadialRiemann.IsTagged (-b) b N (tagL N)) →
    ∃ C : (N : ℕ) → Fin (2*N) → TriangularCovering.TriCylinder,
      PhysicalFamilyConclusion centered b eta
        (physicalPaddedCap centered fractional b eta c) tagU tagL C ∧
      ∀ᶠ N in atTop, 0 < N ∧
        PhysicalBothHalfBounds centered b eta (physicalPaddedCap centered fractional b eta c)
          N (tagU N) (tagL N) (C N)

structure PhysicalPaddedFiniteStatement : Prop where
  cubic_all : ∀ (centered : Bool) (b c : ℝ), 0 < b → (9/2 : ℝ)*b^6 ≤ c →
    ∀ eta : ℝ, 0 < eta → PaddedFiniteAt centered false b eta c
  fractional_threshold : ∀ (centered : Bool) (b c : ℝ), 0 < b → 0 < c →
    ∀ eta : ℝ, 0 < eta → eta*b^2 ≤ (2*(c/b^5)/9)^2 →
      PaddedFiniteAt centered true b eta c
  eventual_strict : ∀ (centered fractional : Bool) (b c : ℝ), 0 < b →
    (if fractional then 0 < c else (9/2 : ℝ)*b^6 ≤ c) →
    ∀ᶠ eta : ℝ in 𝓝[>] 0, PaddedStrictFiniteAt centered fractional b eta c
  eventual_normalized : ∀ (centered fractional : Bool) (b c : ℝ), 0 < b →
    (if fractional then 0 < c else (9/2 : ℝ)*b^6 ≤ c) →
    ∀ᶠ eta : ℝ in 𝓝[>] 0, PaddedNormalizedFiniteAt centered fractional b eta c

end RadialPhysical

end

end OAI
