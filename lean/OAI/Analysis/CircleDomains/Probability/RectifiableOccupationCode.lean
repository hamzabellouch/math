import OAI.Analysis.CircleDomains.Probability.PathOccupation
import OAI.Analysis.CircleDomains.Selection.TagCodeSpace

namespace OAI

/-! A Borel occupation code on the Borel subset of rectifiable paths.
The total extension is zero off that subset; length finiteness is always
checked separately before it is used as physical occupation. -/

open Set MeasureTheory
open scoped ENNReal Classical

noncomputable section

namespace CircleDomainRigidity

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)]

def rectifiableOccupationCode (γ : C(PathTime, X)) : Measure X :=
  if h : BoundedVariationOn γ univ then pathOccupation ⟨γ, h⟩ else 0

omit [BorelSpace X] [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)] in
theorem rectifiableOccupationCode_eq {γ : C(PathTime, X)}
    (hγ : BoundedVariationOn γ univ) :
    rectifiableOccupationCode γ = pathOccupation ⟨γ, hγ⟩ := by
  simp only [rectifiableOccupationCode, dite_eq_left hγ]

theorem measurable_rectifiableOccupationCode :
    Measurable (rectifiableOccupationCode (X := X)) :=
  measurable_pathOccupation.dite measurable_const measurableSet_rectifiablePaths

omit [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)] in
theorem rectifiableOccupationCode_univ {γ : C(PathTime, X)}
    (hγ : BoundedVariationOn γ univ) :
    rectifiableOccupationCode γ univ = eVariationOn γ univ := by
  rw [rectifiableOccupationCode_eq hγ, pathOccupation_univ]

instance (γ : C(PathTime, X)) : IsFiniteMeasure (rectifiableOccupationCode γ) := by
  by_cases hγ : BoundedVariationOn γ univ
  · rw [rectifiableOccupationCode_eq hγ]
    infer_instance
  · simp only [rectifiableOccupationCode, dite_eq_right hγ]
    infer_instance

instance [CompleteSpace X] [SecondCountableTopology X] :
    StandardBorelSpace (RectifiablePath X) :=
  measurableSet_rectifiablePaths.standardBorel

end CircleDomainRigidity

end

end OAI
