import OAI.Geometry.CylinderCovering.Footprints.QuadraticPhysicalFootprintsDefinitions
import OAI.Geometry.CylinderCovering.Radial.PairedSweepDefinitions

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace CylinderCovering.CanonicalFootprintFinite
open RuledApproximation RadialRiemann Footprints

def rotation (z : Space) : Space := !₂[z 1,-z 0,-z 2]

def midpoint (N : ℕ) (i : Fin N) : ℝ :=
  (RadialRiemann.point (-1) 1 N i + RadialRiemann.point (-1) 1 N (i+1))/2

def leftTag (N : ℕ) (i : Fin N) : ℝ := RadialRiemann.point (-1) 1 N i

def absoluteFeet (R : ℝ → ℝ) (A B : ℝ) (N : ℕ) (i : Fin N) : Set (ℝ × ℝ) :=
  absoluteFootprint (midpoint N i) (capMax R (-1) 1 N i) (step (-1) 1 N) A B

def affineFeet (R : ℝ → ℝ) (A B : ℝ) (N : ℕ) (i : Fin N) : Set (ℝ × ℝ) :=
  affineFootprint (midpoint N i) (capMax R (-1) 1 N i) (step (-1) 1 N) A B

def endpointFeet (R : ℝ → ℝ) (ε : ℝ) (N : ℕ) (i : Fin N) : Set (ℝ × ℝ) :=
  endpointFootprint (leftTag N i) (capMax R (-1) 1 N i) (step (-1) 1 N) ε

def localCost (h ε c : ℝ) (F : Set (ℝ × ℝ)) : ℝ :=
  h * volume.real F / Real.sqrt (1+ε^2*(((1+c^2)/2)^2+h^2*c^2))

def FamilyConclusion (h ε : ℝ) (R : ℝ → ℝ)
    (tag : (N : ℕ) → Fin N → ℝ)
    (F : (N : ℕ) → Fin N → Set (ℝ × ℝ)) : Prop :=
  ∃ U L : (N : ℕ) → Fin N → Cylinder,
    (∀ N : ℕ, 0<N →
      (∀ i : Fin N,
        (U N i).axis = RadialPairedSweep.upperAxis h ε (tag N i) ∧
        (L N i).axis = rotation (RadialPairedSweep.upperAxis h ε (tag N i)) ∧
        Subtype.val '' (U N i).base = physicalFootprintProjection h ε (tag N i) '' F N i ∧
        Subtype.val '' (L N i).base = rotation ''
          (physicalFootprintProjection h ε (tag N i) '' F N i) ∧
        IsCompact (U N i).base ∧ IsCompact (L N i).base ∧
        MeasurableSet (U N i).base ∧ MeasurableSet (L N i).base ∧
        volume (U N i).base < ⊤ ∧ volume (L N i).base < ⊤ ∧
        (Convex ℝ (U N i).base ↔ Convex ℝ (F N i)) ∧
        (Convex ℝ (L N i).base ↔ Convex ℝ (F N i)) ∧
        (U N i).area = localCost h ε (tag N i) (F N i) ∧
        (L N i).area = localCost h ε (tag N i) (F N i)) ∧
      RadialPairedSweep.upperSweep h ε R ⊆ familySet (U N) ∧
      RadialPairedSweep.lowerSweep h ε R ⊆ familySet (L N)) ∧
    Tendsto (fun N => familyArea (U N)+familyArea (L N)) atTop
      (𝓝 (2*h*RadialPairedSweep.physicalCost h ε R))

def Statement : Prop :=
  ∀ h ε : ℝ, 0<h → 0≤ε → ∀ R : ℝ → ℝ,
    ContinuousOn R (Icc (-1:ℝ) 1) → (∀ q ∈ Icc (-1:ℝ) 1, 0≤R q) →
    (∀ A B : ℝ, 2*ε≤A → ε≤B →
      ∀ tag : (N : ℕ) → Fin N → ℝ,
        (∀ N, IsTagged (-1) 1 N (tag N)) →
          FamilyConclusion h ε R tag (absoluteFeet R A B)) ∧
    (∀ A B : ℝ, ε≤A → ε/4≤B →
      FamilyConclusion h ε R midpoint (absoluteFeet R A B)) ∧
    (∀ A B : ℝ, ε≤A → 3*ε/4≤B → A/2≤B →
      FamilyConclusion h ε R midpoint (affineFeet R A B)) ∧
    FamilyConclusion h ε R leftTag (endpointFeet R ε)

end CylinderCovering.CanonicalFootprintFinite

end

end OAI
