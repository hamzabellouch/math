import Mathlib

namespace OAI

open MeasureTheory

open scoped NNReal ENNReal

lemma probability_three_complements {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (S T U : Set Ω)
    (hS : MeasurableSet S) (hT : MeasurableSet T) (hU : MeasurableSet U)
    (hμS : μ S ≤ (1/64:ENNReal)) (hμT : μ T ≤ (1/64:ENNReal))
    (hμU : μ U ≤ (1/64:ENNReal)) :
    (1/2:ENNReal) ≤ μ ((S ∪ T ∪ U)ᶜ) := by
  have hb : μ (S ∪ T ∪ U) ≤ (1/64:ENNReal)+(1/64:ENNReal)+(1/64:ENNReal) :=
    (measure_union_le _ _).trans (add_le_add ((measure_union_le _ _).trans (add_le_add hμS hμT)) hμU)
  rw [prob_compl_eq_one_sub ((hS.union hT).union hU)]
  refine le_trans ?_ (tsub_le_tsub_left hb 1)
  apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
  rw [ENNReal.toReal_sub_of_le (by
    apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
    norm_num [ENNReal.toReal_add]) (by finiteness)]
  norm_num [ENNReal.toReal_add]

end OAI
