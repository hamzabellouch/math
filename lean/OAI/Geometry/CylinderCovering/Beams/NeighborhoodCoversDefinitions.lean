import OAI.Geometry.CylinderCovering.Beams.FullDefinitions

namespace OAI

noncomputable section
open Set
namespace ShortenedBeam

def NeighborhoodFamilies (a : ℝ) (N : ℕ)
    (Cm Cp : Fin N → RuledApproximation.Cylinder) : Prop :=
  (∀ i : Fin N,
    (Cm i).axis = axisMinus a (midpointTag N i) ∧
    (Cp i).axis = axisPlus a (midpointTag N i) ∧
    Subtype.val '' (Cm i).base = neighborhoodBaseMinus a N i ∧
    Subtype.val '' (Cp i).base = neighborhoodBasePlus a N i ∧
    IsCompact (Cm i).base ∧ IsCompact (Cp i).base) ∧
  beamMinus a ⊆ RuledApproximation.familySet Cm ∧
  beamPlus a ⊆ RuledApproximation.familySet Cp

def NeighborhoodMixedStatement : Prop :=
  ∀ a : ℝ, 0 < a → a < 1/2 → ∀ ε : ℝ, 0 < ε →
    ∃ N : ℕ, 0 < N ∧
    ∃ Cm Cp : Fin N → RuledApproximation.Cylinder,
    ∃ n : ℕ, ∃ D : Fin n → RuledApproximation.Cylinder,
      NeighborhoodFamilies a N Cm Cp ∧
      (∀ j, CylinderCovering.BeamStrip.IsHorizontalRectangle (D j)) ∧
      strip a ⊆ RuledApproximation.familySet D ∧
      tetrahedron ⊆ (RuledApproximation.familySet Cm ∪
        RuledApproximation.familySet Cp) ∪ RuledApproximation.familySet D ∧
      RuledApproximation.familyArea Cm + RuledApproximation.familyArea Cp +
        RuledApproximation.familyArea D ≤
        (Real.sqrt 2/4)*(CylinderCovering.BeamCost.beamCost a+
          CylinderCovering.BeamCost.stripCost a)+ε

def NeighborhoodStrictStatement : Prop :=
  ∃ a : ℝ, 0 < a ∧ a < 1/2 ∧
    ∃ N : ℕ, 0 < N ∧
    ∃ Cm Cp : Fin N → RuledApproximation.Cylinder,
    ∃ n : ℕ, ∃ D : Fin n → RuledApproximation.Cylinder,
      NeighborhoodFamilies a N Cm Cp ∧
      (∀ j, CylinderCovering.BeamStrip.IsHorizontalRectangle (D j)) ∧
      strip a ⊆ RuledApproximation.familySet D ∧
      tetrahedron ⊆ (RuledApproximation.familySet Cm ∪
        RuledApproximation.familySet Cp) ∪ RuledApproximation.familySet D ∧
      RuledApproximation.familyArea Cm + RuledApproximation.familyArea Cp +
        RuledApproximation.familyArea D < CylinderCovering.minimumShadowArea tetrahedron/2

end ShortenedBeam

end

end OAI
