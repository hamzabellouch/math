import OAI.Analysis.CircleDomains.Probability.PublishedMeasureDuality
import Mathlib.MeasureTheory.MeasurableSpace.CountablyGenerated

namespace OAI

/-! Countably many measurable evaluations distinguish finite measures.
Finite intersections of a generating sequence form the required pi system. -/
open Set Function MeasureTheory MeasurableSpace
open scoped ENNReal
noncomputable section
namespace CircleDomainRigidity
variable (Z : Type*) [MeasurableSpace Z] [CountablyGenerated Z]

def measureCoordinateSet (s : Finset ℕ) : Set Z :=
  ⋂ n ∈ s, natGeneratingSequence Z n

lemma measurableSet_measureCoordinateSet (s : Finset ℕ) :
    MeasurableSet (measureCoordinateSet Z s) := by
  exact MeasurableSet.biInter s.finite_toSet.countable (fun n _ => measurableSet_natGeneratingSequence n)

lemma measureCoordinateSet_union (s t : Finset ℕ) :
    measureCoordinateSet Z (s ∪ t) = measureCoordinateSet Z s ∩ measureCoordinateSet Z t := by
  ext x
  simp only [measureCoordinateSet, mem_iInter, Finset.mem_union, mem_inter_iff]
  aesop

lemma measureCoordinateSet_generates :
    generateFrom (range (measureCoordinateSet Z)) = (inferInstance : MeasurableSpace Z) := by
  apply le_antisymm
  · apply generateFrom_le
    rintro _ ⟨s, rfl⟩
    exact measurableSet_measureCoordinateSet Z s
  · apply (generateFrom_natGeneratingSequence Z).symm.le.trans
    apply generateFrom_mono
    rintro _ ⟨n, rfl⟩
    refine ⟨{n}, ?_⟩
    simp only [measureCoordinateSet, Finset.mem_singleton, iInter_iInter_eq_left]

def finiteMeasureCoordinates (μ : FiniteMeasure Z) (s : Finset ℕ) : ℝ≥0∞ :=
  (μ : Measure Z) (measureCoordinateSet Z s)

lemma measurable_finiteMeasureCoordinates : Measurable (finiteMeasureCoordinates Z) := by
  apply Measurable.of_eval
  intro s
  exact (Measure.measurable_coe (measurableSet_measureCoordinateSet Z s)).comp
    measurable_subtype_coe

lemma injective_finiteMeasureCoordinates : Injective (finiteMeasureCoordinates Z) := by
  intro μ ν h
  apply FiniteMeasure.toMeasure_injective
  apply ext_of_generate_finite (range (measureCoordinateSet Z))
    (measureCoordinateSet_generates Z).symm
  · rintro _ ⟨s, rfl⟩ _ ⟨t, rfl⟩ _
    exact ⟨s ∪ t, measureCoordinateSet_union Z s t⟩
  · rintro _ ⟨s, rfl⟩
    exact congrFun h s
  · have hh := congrFun h ∅
    simpa only [finiteMeasureCoordinates, measureCoordinateSet, Finset.notMem_empty,
      iInter_of_empty, iInter_univ] using hh

end CircleDomainRigidity

end

end OAI
