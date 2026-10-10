import Mathlib

namespace OAI

open MeasureTheory

open scoped NNReal ENNReal

namespace SparseHoles

lemma weighted_moment_markov {Ω ι : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (S : Finset ι) (w : ι → ℝ≥0) (f : ι → Ω → ENNReal)
    (hf : ∀ i∈S, Measurable (f i)) (C : ℝ≥0)
    (hC : ∀ i∈S, ∫⁻ ω, f i ω ∂μ ≤ C) :
    μ {ω | (64:ENNReal)*(C+1)*((∑ i∈S,w i)+1) ≤ ∑ i∈S, (w i:ENNReal)*f i ω} ≤ 1/64 := by
  have hI : (∫⁻ ω,∑ i∈S,(w i:ENNReal)*f i ω ∂μ) ≤ C*(∑ i∈S,w i) := by
    rw [lintegral_finsetSum S (f := fun i ω => (w i:ENNReal)*f i ω) (fun i hi => measurable_const.mul (hf i hi))]
    calc
      _ ≤ ∑ i∈S,(w i:ENNReal)*C := by
        apply Finset.sum_le_sum
        intro i hi
        rw [lintegral_const_mul _ (hf i hi)]
        gcongr;exact hC i hi
      _ = C*(∑ i∈S,w i) := by rw [ENNReal.ofNNReal_finsetSum,Finset.mul_sum];apply Finset.sum_congr rfl;intros;ring
  have hm : Measurable (fun ω => ∑ i∈S,(w i:ENNReal)*f i ω) :=
    Finset.measurable_sum S (fun i hi => show Measurable (fun ω => (w i:ENNReal)*f i ω) from measurable_const.mul (hf i hi))
  have hp : (64*(C+1)*((∑ i∈S,w i)+1):ENNReal) ≠ 0 := by positivity
  have hfin : (64*(C+1)*((∑ i∈S,w i)+1):ENNReal) ≠ ⊤ := by finiteness
  apply (meas_ge_le_lintegral_div hm.aemeasurable hp hfin).trans
  apply ENNReal.div_le_of_le_mul
  apply hI.trans
  have hb : (C:ENNReal)*(∑ i∈S,w i) ≤ (C+1)*((∑ i∈S,w i)+1) := by gcongr;all_goals exact le_self_add
  apply hb.trans_eq
  have he : (1/64:ENNReal)*64=1 := by
    apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
    norm_num
  rw [← mul_assoc,← mul_assoc,he,one_mul]

end SparseHoles

end OAI
