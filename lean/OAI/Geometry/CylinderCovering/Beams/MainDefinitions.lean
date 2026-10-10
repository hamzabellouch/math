import OAI.Geometry.CylinderCovering.Beams.StatementsDefinitions
import OAI.Geometry.CylinderCovering.Beams.StripDefinitions
import OAI.Geometry.CylinderCovering.Convexity.GlobalDefinitions

namespace OAI

noncomputable section
open Set MeasureTheory

namespace ShortenedBeam

def HasTriangularBase (C : RuledApproximation.Cylinder) : Prop :=
  ∃ v : Fin 3 → Space, AffineIndependent ℝ v ∧
    ((fun z : ((Submodule.span ℝ ({C.axis} : Set Space))ᗮ) =>
      (z : Space)) '' C.base) = convexHull ℝ (range v)

def HasMixedBase (C : RuledApproximation.Cylinder) : Prop :=
  HasTriangularBase C ∨ CylinderCovering.BeamStrip.HasRectangularBase C

def FiniteStripStatement : Prop :=
  ∀ a ε : ℝ, 0 < ε →
    RuledApproximation.HasFiniteCover CylinderCovering.BeamStrip.IsHorizontalRectangle
      (strip a) ((Real.sqrt 2/4)*CylinderCovering.BeamCost.stripCost a + ε)

def CoreFiniteMixedStatement : Prop :=
  ∀ a ε : ℝ, 0 < a → a < 1/2 → 0 < ε →
    RuledApproximation.HasFiniteCover HasMixedBase tetrahedron
      ((Real.sqrt 2/4)*(CylinderCovering.BeamCost.beamCost a+
        CylinderCovering.BeamCost.stripCost a)+ε)

def CanonicalCounterexampleStatement : Prop :=
  ∃ n : ℕ, ∃ C : Fin n → RuledApproximation.Cylinder,
    (∀ i, HasMixedBase (C i)) ∧ tetrahedron ⊆ RuledApproximation.familySet C ∧
    RuledApproximation.familyArea C < Real.sqrt 2

def RegularMixedCounterexampleStatement : Prop :=
  ∀ K : Set Space, CylinderCovering.IsRegularTetrahedron K →
    ∃ n : ℕ, ∃ C : Fin n → RuledApproximation.Cylinder,
      (∀ i, HasMixedBase (C i)) ∧ K ⊆ RuledApproximation.familySet C ∧
      RuledApproximation.familyArea C < CylinderCovering.minimumShadowArea K / 2 ∧
      CylinderCovering.relativeCost K C < 1/2

end ShortenedBeam

end

end OAI
