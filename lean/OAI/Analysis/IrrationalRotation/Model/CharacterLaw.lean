import Mathlib.Analysis.Fourier.AddCircleMulti
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

namespace OAI

noncomputable section

namespace Invariant233.CharacterLaws

open MeasureTheory

def circleHaar : ProbabilityMeasure (AddCircle (1 : ℝ)) :=
  ⟨volume, ⟨by simp [AddCircle.measure_univ]⟩⟩

def torusHaar (m : ℕ) : ProbabilityMeasure (UnitAddTorus (Fin m)) := by
  letI : IsProbabilityMeasure (volume : Measure (AddCircle (1 : ℝ))) :=
    circleHaar.property
  exact ⟨volume, inferInstance⟩

def characterMap {m : ℕ} (q : Fin m → ℕ) :
    C(AddCircle (1 : ℝ), UnitAddTorus (Fin m)) :=
  ⟨fun x i => (q i : ℤ) • x, by fun_prop⟩

def characterLaw {m : ℕ} (q : Fin m → ℕ) : ProbabilityMeasure (UnitAddTorus (Fin m)) :=
  circleHaar.map (characterMap q)

def characterPhaseLaw {Z : Type*} [TopologicalSpace Z] [MeasurableSpace Z]
    [BorelSpace Z] {m : ℕ} (q : Fin m → ℕ) (a : Z) :
    ProbabilityMeasure (Z × UnitAddTorus (Fin m)) :=
  circleHaar.map (fun x => (a, characterMap q x))

def haarPhaseLaw {Z : Type*} [TopologicalSpace Z] [MeasurableSpace Z]
    [BorelSpace Z] (m : ℕ) (a : Z) : ProbabilityMeasure (Z × UnitAddTorus (Fin m)) :=
  (torusHaar m).map (fun y => (a, y))

end Invariant233.CharacterLaws

end

end OAI
