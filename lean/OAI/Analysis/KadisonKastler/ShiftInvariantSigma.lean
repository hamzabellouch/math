import Mathlib.MeasureTheory.Measure.QuasiMeasurePreserving
import Mathlib.MeasureTheory.Measure.Trim
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

namespace OAI

/-! # The invariant sigma algebra of the nonsingular boundary shift

Using this measurable space directly avoids a redundant point-set coding of
the boundary. Its measurable sets are exactly the ambient measurable sets
fixed by the shift modulo null sets.
-/

namespace KadisonKastler

noncomputable section

open MeasureTheory Set

variable {X : Type*} [MeasurableSpace X] (μ : Measure X) (S : X → X)

@[instance_reducible]
def shiftInvariantSigma : MeasurableSpace X where
  MeasurableSet' A := MeasurableSet A ∧ ∀ᵐ x ∂μ, S x ∈ A ↔ x ∈ A
  measurableSet_empty := ⟨MeasurableSet.empty, Filter.Eventually.of_forall (by simp)⟩
  measurableSet_compl A hA := ⟨hA.1.compl, hA.2.mono (fun _ h => not_congr h)⟩
  measurableSet_iUnion A hA := by
    refine ⟨MeasurableSet.iUnion (fun n => (hA n).1), ?_⟩
    filter_upwards [ae_all_iff.mpr (fun n => (hA n).2)] with x hx
    simpa only [Set.mem_iUnion] using exists_congr hx

theorem shiftInvariantSigma_le : shiftInvariantSigma μ S ≤ ‹MeasurableSpace X› :=
  fun _ h => h.1

def shiftInvariantMeasure : @Measure X (shiftInvariantSigma μ S) :=
  μ.trim (shiftInvariantSigma_le μ S)

instance shiftInvariantMeasure_probability [IsProbabilityMeasure μ] :
    @IsProbabilityMeasure X (shiftInvariantSigma μ S) (shiftInvariantMeasure μ S) := by
  constructor
  rw [shiftInvariantMeasure, trim_measurableSet_eq _ MeasurableSet.univ]
  exact measure_univ

theorem shiftInvariantSigma_of_null
    (hS : Measure.QuasiMeasurePreserving S μ μ) {A : Set X}
    (hA : MeasurableSet A) (hzero : μ A = 0) :
    MeasurableSet[shiftInvariantSigma μ S] A := by
  refine ⟨hA, ?_⟩
  have hn : ∀ᵐ x ∂μ, x ∉ A := by
    rw [ae_iff]
    simpa only [not_not, Set.ofPred_mem_eq] using hzero
  filter_upwards [hn, hS.ae hn] with x hx hs
  simp only [hx, hs]

theorem measurable_shiftInvariantSigma_of_fixed
    {Y : Type*} [MeasurableSpace Y] {f : X → Y} (hf : Measurable f)
    (hfixed : ∀ᵐ x ∂μ, f (S x) = f x) :
    Measurable[shiftInvariantSigma μ S] f := by
  intro A hA
  refine ⟨hf hA, hfixed.mono ?_⟩
  intro x hx
  change f (S x) ∈ A ↔ f x ∈ A
  rw [hx]

theorem measurable_shiftInvariantSigma_of_commuting
    (T : X → X) (hT : Measure.QuasiMeasurePreserving T μ μ)
    (hcomm : ∀ x, S (T x) = T (S x)) :
    @Measurable X X (shiftInvariantSigma μ S) (shiftInvariantSigma μ S) T := by
  intro A hA
  refine ⟨hT.measurable hA.1, ?_⟩
  filter_upwards [hT.ae hA.2] with x hx
  change T (S x) ∈ A ↔ T x ∈ A
  rw [← hcomm]
  exact hx

theorem quasi_shiftInvariantSigma_of_commuting
    (T : X → X) (hT : Measure.QuasiMeasurePreserving T μ μ)
    (hcomm : ∀ x, S (T x) = T (S x)) :
    @Measure.QuasiMeasurePreserving X X (shiftInvariantSigma μ S) (shiftInvariantSigma μ S)
      T (shiftInvariantMeasure μ S) (shiftInvariantMeasure μ S) := by
  have hm := measurable_shiftInvariantSigma_of_commuting μ S T hT hcomm
  refine ⟨hm, Measure.AbsolutelyContinuous.mk ?_⟩
  intro A hA hzero
  have hzero' : μ A = 0 := by
    rwa [shiftInvariantMeasure, trim_measurableSet_eq _ hA] at hzero
  rw [Measure.map_apply hm hA, shiftInvariantMeasure,
    trim_measurableSet_eq _ (hm hA)]
  exact hT.preimage_null hzero'

end

end KadisonKastler

end OAI
