import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import OAI.Analysis.IrrationalRotation.Model.UnrestrictedDiagonal
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.MeasureTheory.Measure.Map

namespace OAI

open MeasureTheory
open scoped NNReal
noncomputable section

namespace Invariant233

instance sequenceHilbertIntMeasurableSpace : MeasurableSpace (SequenceHilbert ℤ) := borel _

instance sequenceHilbertIntBorelSpace : BorelSpace (SequenceHilbert ℤ) := ⟨rfl⟩

def UniformlyAbsolutelyContinuous {X ι : Type*} [MeasurableSpace X]
    (μ : Measure X) (ν : ι → Measure X) : Prop :=
  ∀ ε : ℝ≥0, 0 < ε → ∃ δ : ℝ≥0, 0 < δ ∧
    ∀ A : Set X, MeasurableSet A → μ A < δ → ∀ i, ν i A < ε

noncomputable def ratioDiagonal {X : Type*} (F : ℤ → X → ℝ) (t : X × X) :
    SequenceHilbert ℤ →L[ℂ] SequenceHilbert ℤ :=
  SequenceHilbert.boundedDiagonal (fun i => ((F i t.2 / F i t.1 : ℝ) : ℂ))

end Invariant233

end

end OAI
