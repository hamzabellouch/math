import OAI.Geometry.CylinderCovering.Rational.ConstructionDefinitions
import OAI.Geometry.CylinderCovering.Convexity.OpenParallelogramDefinitions

namespace OAI

namespace SlopeRational

open RuledApproximation

structure StrictOpenEnlargement {n m : ℕ}
    (C : Fin n → Cylinder) (D : Fin m → Cylinder)
    (U : Fin n → Cylinder) (V : Fin m → Cylinder) : Prop where
  first_axes : ∀ i, (U i).axis = (C i).axis
  second_axes : ∀ j, (V j).axis = (D j).axis
  first_shape : ∀ i, (U i).openParallelogram ∧ (U i).openBounded
  second_shape : ∀ j, (V j).openParallelogram ∧ (V j).openBounded
  first_cylinders : ∀ i, (C i).carrier ⊆ (U i).carrier
  second_cylinders : ∀ j, (D j).carrier ⊆ (V j).carrier
  first_contains : familySet C ⊆ familySet U
  second_contains : familySet D ⊆ familySet V
  area_lt : familyArea U + familyArea V < physicalScale / 4
  relative_lt : CylinderCovering.relativeCost referenceTetrahedron U +
    CylinderCovering.relativeCost referenceTetrahedron V < 1 / 2

def HasStrictFiniteOpenCover (d ε q : ℝ) : Prop :=
  ∃ n m : ℕ, ∃ C : Fin n → Cylinder, ∃ D : Fin m → Cylinder,
    ∃ U : Fin n → Cylinder, ∃ V : Fin m → Cylinder,
    (∀ i, (C i).parallelogram) ∧ (∀ j, (D j).parallelogram) ∧
    lowerSweep d ε q ⊆ familySet C ∧ upperSweep d ε q ⊆ familySet D ∧
    referenceTetrahedron ⊆ familySet C ∪ familySet D ∧
    familyArea C + familyArea D < physicalScale / 4 ∧
    StrictOpenEnlargement C D U V

open Filter
open scoped Topology

def OpenPaddingSchedulesStatement : Prop :=
  (∃ d : ℝ, 0 < d ∧ 0 < coefficientGap d) ∧
  (∀ d : ℝ, 0 < d → 0 < coefficientGap d →
    (∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ),
      weightedCost d ε (ε ^ (5 / 2 : ℝ)) < physicalScale / 8 ∧
      HasStrictFiniteOpenCover d ε (ε ^ (5 / 2 : ℝ))) ∧
    ∀ η : ℝ, 0 < η → η / 2 < coefficientGap d →
      ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ),
        weightedCost d ε (η * ε ^ 2) < physicalScale / 8 ∧
        HasStrictFiniteOpenCover d ε (η * ε ^ 2))

end SlopeRational

end OAI
