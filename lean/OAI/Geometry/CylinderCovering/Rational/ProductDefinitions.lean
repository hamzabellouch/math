import OAI.Geometry.CylinderCovering.Rational.ConstructionDefinitions

namespace OAI

noncomputable section
open Set Filter
open scoped Topology

namespace SlopeRational

def ProductApproximationStatement : Prop :=
  ∀ d ε : ℝ, 0 < d → 0 < ε → ε < 8 * d → ∀ q e : ℝ, 0 < e →
    RuledApproximation.HasFiniteCover RuledApproximation.Cylinder.openBounded
      (lowerSweep d ε q) (weightedCost d ε q + e) ∧
    RuledApproximation.HasFiniteCover RuledApproximation.Cylinder.openBounded
      (upperSweep d ε q) (weightedCost d ε q + e)

def HasStrictOpenFiniteCover (d ε q : ℝ) : Prop :=
  ∃ n m : ℕ, ∃ C : Fin n → RuledApproximation.Cylinder,
    ∃ D : Fin m → RuledApproximation.Cylinder,
    (∀ i, (C i).openBounded) ∧ (∀ j, (D j).openBounded) ∧
    lowerSweep d ε q ⊆ RuledApproximation.familySet C ∧
    upperSweep d ε q ⊆ RuledApproximation.familySet D ∧
    referenceTetrahedron ⊆ RuledApproximation.familySet C ∪ RuledApproximation.familySet D ∧
    RuledApproximation.familyArea C + RuledApproximation.familyArea D < physicalScale / 4 ∧
    CylinderCovering.relativeCost referenceTetrahedron C +
      CylinderCovering.relativeCost referenceTetrahedron D < 1 / 2

def ProductFractionalStatement : Prop :=
  (∃ d : ℝ, 0 < d ∧ 0 < coefficientGap d) ∧
  ∀ d : ℝ, 0 < d → 0 < coefficientGap d →
    ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ),
      weightedCost d ε (ε ^ (5 / 2 : ℝ)) < physicalScale / 8 ∧
      HasStrictOpenFiniteCover d ε (ε ^ (5 / 2 : ℝ))

def ProductRealizationStatement : Prop :=
  ProductApproximationStatement ∧ ProductFractionalStatement

end SlopeRational

end

end OAI
