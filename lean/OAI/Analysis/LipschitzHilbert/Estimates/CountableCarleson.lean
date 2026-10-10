import OAI.Analysis.LipschitzHilbert.Estimates.CarlesonExponential
import Mathlib.MeasureTheory.Measure.Continuity
import Mathlib.MeasureTheory.Constructions.Polish.Basic

namespace OAI

/-!
# Countable exhaustion of the Carleson tail

The count is an actual ENNReal sum over occurrences. Every finite subset
has the same exponential tail bound, so continuity from below gives that
bound for the full count without requiring a choice of enumeration.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal

namespace LipschitzHilbert

variable {ι X : Type*} [Countable ι] [MeasurableSpace X]

attribute [local instance] Classical.propDecidable

def occurrenceCount (Q : ι → Set X) (x : X) : ℝ≥0∞ :=
  ∑' i, (Q i).indicator (1 : X → ℝ≥0∞) x

def finiteOccurrenceCount (Q : ι → Set X) (s : Finset ι) (x : X) : ℝ :=
  ∑ i ∈ s, (Q i).indicator (1 : X → ℝ) x

theorem measurable_occurrenceCount (Q : ι → Set X) (hQ : ∀ i, MeasurableSet (Q i)) :
    Measurable (occurrenceCount Q) :=
  Measurable.tsum fun i => measurable_one.indicator (hQ i)

omit [Countable ι] in
theorem measurable_finiteOccurrenceCount (Q : ι → Set X) (hQ : ∀ i, MeasurableSet (Q i))
    (s : Finset ι) : Measurable (finiteOccurrenceCount Q s) :=
  Finset.measurable_sum s fun i _ => measurable_one.indicator (hQ i)

omit [Countable ι] [MeasurableSpace X] in
theorem finiteOccurrenceCount_nonneg (Q : ι → Set X) (s : Finset ι) (x : X) :
    0 ≤ finiteOccurrenceCount Q s x := by
  apply Finset.sum_nonneg
  intro i _
  by_cases hx : x ∈ Q i <;> simp [Set.indicator, hx]

omit [Countable ι] [MeasurableSpace X] in
theorem finiteOccurrenceCount_mono (Q : ι → Set X) {s t : Finset ι} (hst : s ⊆ t) (x : X) :
    finiteOccurrenceCount Q s x ≤ finiteOccurrenceCount Q t x := by
  apply Finset.sum_le_sum_of_subset_of_nonneg hst
  intro i _ _
  by_cases hx : x ∈ Q i <;> simp [Set.indicator, hx]

omit [Countable ι] [MeasurableSpace X] in
theorem ofReal_finiteOccurrenceCount (Q : ι → Set X) (s : Finset ι) (x : X) :
    ENNReal.ofReal (finiteOccurrenceCount Q s x) =
      ∑ i ∈ s, (Q i).indicator (1 : X → ℝ≥0∞) x := by
  unfold finiteOccurrenceCount
  rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => by
    by_cases hx : x ∈ Q i <;> simp [Set.indicator, hx])]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hx : x ∈ Q i <;> simp [Set.indicator, hx]

omit [Countable ι] [MeasurableSpace X] in
theorem occurrenceCount_superlevel_eq_iUnion (Q : ι → Set X) {lambda : ℝ}
    (hlambda : 0 ≤ lambda) :
    {x | ENNReal.ofReal lambda < occurrenceCount Q x} =
      ⋃ s : Finset ι, {x | lambda < finiteOccurrenceCount Q s x} := by
  ext x
  simp only [Set.mem_ofPred_eq, occurrenceCount, ENNReal.tsum_eq_iSup_sum, lt_iSup_iff,
    Set.mem_iUnion]
  apply exists_congr
  intro s
  rw [← ofReal_finiteOccurrenceCount, ENNReal.ofReal_lt_ofReal_iff_of_nonneg hlambda]

/-- Uniform bounds on every finite subcount pass to the actual countable
sum. This is the monotone-convergence step in `count:line-lemma`. -/
theorem occurrenceCount_tail_of_finite (Q : ι → Set X) (μ : Measure X) [IsFiniteMeasure μ]
    {lambda B : ℝ} (hlambda : 0 ≤ lambda) (hB : 0 ≤ B)
    (hfinite : ∀ s : Finset ι, μ.real {x | lambda < finiteOccurrenceCount Q s x} ≤ B) :
    μ.real {x | ENNReal.ofReal lambda < occurrenceCount Q x} ≤ B := by
  rw [occurrenceCount_superlevel_eq_iUnion Q hlambda]
  have hdir : Directed (· ⊆ ·) (fun s : Finset ι => {x | lambda < finiteOccurrenceCount Q s x}) := by
    intro s t
    refine ⟨s ∪ t, ?_, ?_⟩
    · intro x hx
      exact hx.trans_le (finiteOccurrenceCount_mono Q Finset.subset_union_left x)
    · intro x hx
      exact hx.trans_le (finiteOccurrenceCount_mono Q Finset.subset_union_right x)
  apply ENNReal.toReal_le_of_le_ofReal hB
  rw [hdir.measure_iUnion]
  apply iSup_le
  intro s
  exact (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top μ _) hB).2 (hfinite s)

/-- The same exhaustion bound on a finite-measure root, even when the
ambient measure is infinite, as for Lebesgue measure on the line. -/
theorem occurrenceCount_root_tail_of_finite (Q : ι → Set X) (μ : Measure X)
    (hQ : ∀ i, MeasurableSet (Q i)) {P : Set X} (hPfinite : μ P ≠ ⊤)
    {lambda B : ℝ} (hlambda : 0 ≤ lambda) (hB : 0 ≤ B)
    (hfinite : ∀ s : Finset ι,
      μ.real ({x | lambda < finiteOccurrenceCount Q s x} ∩ P) ≤ B) :
    μ.real ({x | ENNReal.ofReal lambda < occurrenceCount Q x} ∩ P) ≤ B := by
  have : IsFiniteMeasure (μ.restrict P) := isFiniteMeasure_restrict.mpr hPfinite
  have h := occurrenceCount_tail_of_finite Q (μ.restrict P) hlambda hB (fun s => by
    simpa only [measureReal_restrict_apply (measurableSet_lt measurable_const
      (measurable_finiteOccurrenceCount Q hQ s))] using hfinite s)
  simpa only [measureReal_restrict_apply (measurableSet_lt measurable_const
    (measurable_occurrenceCount Q hQ))] using h

end LipschitzHilbert

end

end OAI
