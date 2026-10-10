import Mathlib
import OAI.Analysis.CoulombRadii.RandomFields.ObservedUnordered

namespace OAI

section
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical
noncomputable section
namespace NeutralAtom

lemma rawCount_le_displaced {n : ℕ} {S T : Set Position}
    (x v : Configuration n) {d : ℝ}
    (hdisp : ∀ i,‖x i-v i‖ ≤ d)
    (hST : ∀ a∈S,∀ b,‖a-b‖ ≤ d → b∈T) : rawCount S x ≤ rawCount T v := by
  apply Finset.sum_le_sum
  intro i _
  by_cases hi : x i∈S
  · simp only [Set.indicator_of_mem hi,Set.indicator_of_mem (hST _ hi _ (hdisp i)),le_refl]
  · rw [Set.indicator_of_notMem hi]
    exact Set.indicator_nonneg (fun _ _ => by norm_num) _

lemma physical_observed_count_measurable {n J : ℕ} (r : Fin J → ℝ)
    (j : ℕ) (k : Fin J) (hk : j ≤ k.val) {S : Set Position} (hS : MeasurableSet S) :
    StronglyMeasurable[observationSigma (n:=n) r j]
      (fun sample => rawCount S (observedOrdered r k sample)) := by
  have H := unorderedSum_tail_stronglyMeasurable (n:=n) r j k
    (measurable_const.indicator hS : Measurable (S.indicator (fun _ => (1:ℝ))))
  simpa only [tailObservation,ite_eq_left hk,observedArray,unorderedSum_forgetOrder,rawCount] using H

lemma posterior_count_le_observed {n J : ℕ} (ν : Measure (Configuration n))
    [IsProbabilityMeasure ν] (r : Fin J → ℝ) (hr : ∀ k,0 ≤ r k)
    {j : ℕ} (k : Fin J) (hk : j ≤ k.val) {S T : Set Position}
    (hS : MeasurableSet S) (hT : MeasurableSet T)
    (hST : ∀ a∈S,∀ b,‖a-b‖ ≤ Real.sqrt 3*(r k)^(101/100:ℝ) → b∈T) :
    ∀ᵐ sample ∂observationLaw J ν,
      (∫ x,rawCount S x ∂ProbabilityTheory.condDistrib Prod.fst (tailObservation r j)
        (observationLaw J ν) (tailObservation r j sample)) ≤ rawCount T (observedOrdered r k sample) := by
  let P := observationLaw J ν
  let f := fun sample : ObservationSample n J => rawCount S sample.1
  let H := fun sample : ObservationSample n J => rawCount T (observedOrdered r k sample)
  have hfν : Integrable (rawCount (n:=n) S) ν := by
    apply Integrable.of_bound (measurable_rawCount hS).aestronglyMeasurable (n:ℝ)
    filter_upwards [] with x
    rw [Real.norm_of_nonneg (rawCount_nonneg S x)]
    exact rawCount_le_number S x
  have hf : Integrable f P := (observationLaw_rawProjection ν).integrable_comp_of_integrable hfν
  have hHm := physical_observed_count_measurable (n:=n) r j k hk hT
  have hH : Integrable H P := by
    apply Integrable.of_bound (hHm.mono (observationSigma_le r j)).aestronglyMeasurable (n:ℝ)
    filter_upwards [] with sample
    rw [Real.norm_of_nonneg (rawCount_nonneg T _)]
    exact rawCount_le_number T _
  have hle : ∀ᵐ sample ∂P,f sample ≤ H sample := by
    filter_upwards [observationLaw_ae_displacement ν r hr] with sample hh
    exact rawCount_le_displaced sample.1 (observedOrdered r k sample) (hh k) hST
  have Hle := condExp_mono hf hH hle (m:=observationSigma r j)
  rw [condExp_of_stronglyMeasurable (observationSigma_le r j) hHm hH] at Hle
  have He := ProbabilityTheory.condExp_ae_eq_integral_condDistrib
    (measurable_tailObservation r j) (observationLaw_rawProjection ν).measurable.aemeasurable
    (measurable_rawCount hS).stronglyMeasurable hf
  filter_upwards [Hle,He] with sample hh he
  rw [←he]
  exact hh
end NeutralAtom
end

end

end OAI
