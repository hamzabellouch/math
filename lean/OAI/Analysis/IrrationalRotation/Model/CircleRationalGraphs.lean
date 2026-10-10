import OAI.Analysis.IrrationalRotation.Model.ParameterCircleWeights
import OAI.Analysis.IrrationalRotation.Model.CompactTransfer
import Mathlib.MeasureTheory.Measure.FiniteMeasure

namespace OAI

noncomputable section
open MeasureTheory

namespace Invariant233

def circleTranslationGraph (t : Circle) : FiniteMeasure (Circle × Circle) :=
  ⟨circleMeasure.map (fun x => (x, x + t)), by
    change IsFiniteMeasure ((volume : Measure Circle).map (fun x => (x, x + t)))
    infer_instance⟩

namespace CircleParameterData

def rationalTranslation (p : CircleParameterData) (A : ℕ) (r : ℤ) : Circle :=
  (((r : ℝ) / (p.q A : ℝ) : ℝ) : Circle)

def rationalRatioBound (p : CircleParameterData) (A : ℕ) : ℝ :=
  Real.exp (∑ i ∈ Finset.range (A - 1), p.flattenedCost i)

def RationalGraphIdentities (p : CircleParameterData) (θ : ℝ)
    (P : Circle → SequenceHilbert ℤ →L[ℂ] SequenceHilbert ℤ) : Prop :=
  ∀ᵐ x ∂circleMeasure, ∀ A : ℕ, 1 ≤ A → ∀ r : ℤ,
    (1 - P (x + p.rationalTranslation A r)) *
      ratioDiagonal (p.floorCocycle θ) (x, x + p.rationalTranslation A r) * P x = 0

end CircleParameterData
end Invariant233

end

end OAI
