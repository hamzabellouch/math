import OAI.Geometry.RuledCovering.Model

namespace OAI

noncomputable section
open Set MeasureTheory
namespace RuledApproximation

def Cylinder.shadowArea (C : Cylinder) (S : Set Space) : ℝ :=
  volume.real (((Submodule.span ℝ ({C.axis} : Set Space))ᗮ).orthogonalProjectionOnto '' S)

def familyRelativeArea {n : ℕ} (C : Fin n → Cylinder) (S : Set Space) : ℝ :=
  ∑ i, (C i).area / (C i).shadowArea S

def OpenApproximationStatement : Prop :=
  ∀ (n : ℕ) (C : Fin n → Cylinder) (S : Set Space) (m : ℝ),
    (∀ i, IsCompact (C i).base) → S ⊆ familySet C → 0 < m →
    (∀ i, m ≤ (C i).shadowArea S) → familyArea C < m / 2 →
    ∃ D : Fin n → Cylinder,
      (∀ i, (D i).axis = (C i).axis) ∧
      (∀ i, (D i).openBounded) ∧ S ⊆ familySet D ∧
      familyArea D < m / 2 ∧ familyRelativeArea D S < 1 / 2

end RuledApproximation

end

end OAI
