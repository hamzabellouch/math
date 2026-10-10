import OAI.Combinatorics.EditApproximation.Refinement.ComputedExecutionLaw
import OAI.Combinatorics.EditApproximation.Binary.IntegerSymbols

namespace OAI

/-! The uniform algorithm on explicitly stored integer symbols, together
with its conditional accuracy theorem. The hypothesis is a finite scalar
Bernstein bound for the two computed finite product laws. -/

namespace EditApproximation

open MeasureTheory

def ComputedBernsteinInputs (N : ℕ) : Prop :=
  FiniteBernsteinInput (Measure.pi fun _ : Fin (integerParameters N).B =>
    (PMF.uniformOfFintype (Fin (integerParameters N).B)).toMeasure) ∧
  ∀ b : ℕ, ∀ h : Fin (groupDyadicScales (integerParameters N).M b (inputSmallLog N)).length,
    FiniteBernsteinInput (Measure.pi fun _ : Fin
      (groupSampleCount (integerParameters N).M (inputSmallLog N ^ 80) b
        (groupDyadicScaleAt (integerParameters N).M b (inputSmallLog N) h)) =>
      (PMF.uniformOfFintype (Fin (integerParameters N).M)).toMeasure)

abbrev IntegerApproximationOutcome (source target : List ℤ) :=
  ComputedFullOutcome (source.map integerSymbolCode) (target.map integerSymbolCode)
    (source.length + target.length)

noncomputable def integerApproximationLaw (source target : List ℤ) (epsilon : BinaryFraction) :
    Measure (IntegerApproximationOutcome source target) :=
  computedFullLaw (source.map integerSymbolCode) (target.map integerSymbolCode)
    (source.length + target.length) epsilon

noncomputable def integerApproximationAnswer (source target : List ℤ)
    (outcome : IntegerApproximationOutcome source target) : ℕ :=
  computedFullAnswer (source.map integerSymbolCode) (target.map integerSymbolCode)
    (source.length + target.length) outcome

 theorem integerApproximationAnswer_equal (source target : List ℤ) (heq : source = target)
    (outcome : IntegerApproximationOutcome source target) :
    integerApproximationAnswer source target outcome = 0 :=
  computedFullAnswer_equal _ _ _ (congrArg (List.map integerSymbolCode) heq) outcome

 theorem integerApproximation_conditional_accuracy (source target : List ℤ)
    (epsilon : BinaryFraction) (hepsilon : 0 < epsilon.value)
    (bernstein : ComputedBernsteinInputs (source.length + target.length)) :
    (2 / 3 : ℝ) ≤ (integerApproximationLaw source target epsilon).real
      {outcome | EditDistortion.edit source target ≤ integerApproximationAnswer source target outcome ∧
        (integerApproximationAnswer source target outcome : ℝ) ≤
          (1 + (epsilon.value : ℝ)) * EditDistortion.edit source target} := by
  have h := computed_full_conditional_accuracy (source.map integerSymbolCode)
    (target.map integerSymbolCode) (source.length + target.length) epsilon hepsilon
    (by simp only [List.length_map, le_refl]) bernstein.1 bernstein.2
  simpa only [integerSymbols_edit, integerApproximationLaw, integerApproximationAnswer] using h

end EditApproximation

end OAI
