import Mathlib.MeasureTheory.MeasurableSpace.CountablyGenerated
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.PiSystem

namespace OAI

/-! # A countable determining family for finite measures

Finite intersections of a countable measurable generator form a countable
pi system. Equality on this family and equality of total mass determine a
finite measure. This permits simultaneous statements about conditional kernels.
-/

noncomputable section

namespace PolycyclicRecognition

open MeasureTheory MeasurableSpace Set

variable (X : Type*) [mX : MeasurableSpace X] [CountablyGenerated X]

/-- Finite intersections, including the empty intersection. -/
def finiteMeasureTest (I : Finset ℕ) : Set X :=
  ⋂ i ∈ I, natGeneratingSequence X i

theorem measurableSet_finiteMeasureTest (I : Finset ℕ) :
    MeasurableSet (finiteMeasureTest X I) := by
  exact MeasurableSet.iInter (fun i => MeasurableSet.iInter (fun _ =>
    measurableSet_natGeneratingSequence i))

theorem finiteMeasureTest_union (I J : Finset ℕ) :
    finiteMeasureTest X (I ∪ J) = finiteMeasureTest X I ∩ finiteMeasureTest X J := by
  ext x
  simp only [finiteMeasureTest, mem_iInter, Finset.mem_union, mem_inter_iff]
  constructor
  · intro h
    exact ⟨fun i hi => h i (Or.inl hi), fun i hi => h i (Or.inr hi)⟩
  · rintro ⟨hI, hJ⟩ i (hi | hi)
    · exact hI i hi
    · exact hJ i hi

theorem isPiSystem_finiteMeasureTest : IsPiSystem (range (finiteMeasureTest X)) := by
  rintro s ⟨I, rfl⟩ t ⟨J, rfl⟩ _
  exact ⟨I ∪ J, finiteMeasureTest_union X I J⟩

theorem generateFrom_finiteMeasureTest :
    generateFrom (range (finiteMeasureTest X)) = mX := by
  apply le_antisymm
  · exact generateFrom_le (fun s ⟨I, hI⟩ => hI ▸ measurableSet_finiteMeasureTest X I)
  · apply (generateFrom_natGeneratingSequence X).symm.le.trans
    apply generateFrom_mono
    rintro s ⟨i, rfl⟩
    exact ⟨{i}, by ext x; simp [finiteMeasureTest]⟩

/-- A countable determining test suitable for probability kernels. -/
theorem measure_eq_of_finiteMeasureTests (μ ν : Measure X) [IsFiniteMeasure μ]
    (h : ∀ I, μ (finiteMeasureTest X I) = ν (finiteMeasureTest X I)) : μ = ν := by
  apply ext_of_generate_finite (range (finiteMeasureTest X))
    (generateFrom_finiteMeasureTest X).symm (isPiSystem_finiteMeasureTest X)
  · rintro s ⟨I, rfl⟩
    exact h I
  · simpa [finiteMeasureTest] using h ∅

end PolycyclicRecognition

end

end OAI
