import OAI.Analysis.IrrationalRotation.Model.OneCoordinateCoupling

namespace OAI

noncomputable section
open MeasureTheory
open scoped ENNReal

namespace Invariant233.OneCoordinateCoupling

def triangleLaw : Measure (ℝ × ℝ) :=
  (baseLaw.prod baseLaw).restrict {z | z.1 < z.2}

def componentLaw (m a b : ℝ) : Option (Fin 5) → Measure (ℝ × ℝ)
  | none => CouplingMixture.diagonal baseLaw
  | some i => (leftLaw m a b i).prod (rightLaw m a b i)

def componentReference : Option (Fin 5) → Measure (ℝ × ℝ)
  | none => CouplingMixture.diagonal baseLaw
  | some _ => triangleLaw

def replacementDensity (m a b : ℝ) (i : Fin 5) (z : ℝ × ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (leftDensity m a b i z.1) *
    ENNReal.ofReal (rightDensity m a b i z.2)

end Invariant233.OneCoordinateCoupling

end

end OAI
