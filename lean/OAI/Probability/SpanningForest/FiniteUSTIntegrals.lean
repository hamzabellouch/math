import OAI.Probability.SpanningForest.FiniteUSTMeasure

namespace OAI

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal Classical

namespace Problem336

lemma finiteUSTMeasure_ae_treeOn (K : FiniteSubgraphCode) :
    ∀ᵐ X ∂finiteUSTMeasure K,
      ∃ T, TreeOn K T ∧ finiteTreeConfiguration T = X := by
  filter_upwards [finiteUSTMeasure_concentrated K] with X hX
  obtain ⟨T, hT, rfl⟩ := hX
  refine ⟨T, ?_, rfl⟩
  exact (Finset.mem_filter.mp hT).2

lemma lintegral_finiteUSTMeasure (K : FiniteSubgraphCode)
    (f : EdgeConfiguration → ℝ≥0∞) :
    (∫⁻ X, f X ∂finiteUSTMeasure K) =
      (∑ T ∈ spanningTrees K, f (finiteTreeConfiguration T)) /
        (↑(spanningTrees K).card : ℝ≥0∞) := by
  simp only [finiteUSTMeasure, lintegral_smul_measure,
    lintegral_finsetSum_measure, lintegral_dirac, smul_eq_mul,
    ENNReal.div_eq_inv_mul]

lemma integrable_finiteUSTMeasure (K : FiniteSubgraphCode)
    (f : EdgeConfiguration → ℝ) : Integrable f (finiteUSTMeasure K) := by
  classical
  by_cases hK : (spanningTrees K).Nonempty
  · unfold finiteUSTMeasure
    apply Integrable.smul_measure
      (integrable_finsetSum_measure.mpr (fun T _ => integrable_dirac (by simp)))
    exact ENNReal.inv_ne_top.mpr (by exact_mod_cast hK.card_pos.ne')
  · rw [finiteUSTMeasure_eq_zero K (Finset.not_nonempty_iff_eq_empty.mp hK)]
    exact integrable_zero_measure

lemma integral_finiteUSTMeasure (K : FiniteSubgraphCode)
    (f : EdgeConfiguration → ℝ) :
    (∫ X, f X ∂finiteUSTMeasure K) =
      (∑ T ∈ spanningTrees K, f (finiteTreeConfiguration T)) /
        (↑(spanningTrees K).card : ℝ) := by
  rw [finiteUSTMeasure, integral_smul_measure,
    integral_finsetSum_measure (fun T _ => integrable_dirac (by simp))]
  simp only [integral_dirac, ENNReal.toReal_inv, ENNReal.toReal_natCast,
    smul_eq_mul, div_eq_mul_inv, mul_comm]

lemma integral_ratio_finiteUSTMeasure (K : FiniteSubgraphCode)
    (hK : (spanningTrees K).Nonempty) (f g : EdgeConfiguration → ℝ) :
    (∫ X, f X ∂finiteUSTMeasure K) / (∫ X, g X ∂finiteUSTMeasure K) =
      (∑ T ∈ spanningTrees K, f (finiteTreeConfiguration T)) /
        (∑ T ∈ spanningTrees K, g (finiteTreeConfiguration T)) := by
  rw [integral_finiteUSTMeasure, integral_finiteUSTMeasure]
  exact div_div_div_cancel_right₀ (by exact_mod_cast hK.card_pos.ne') _ _

lemma integral_finiteUSTMeasure_pos (K : FiniteSubgraphCode)
    (hK : (spanningTrees K).Nonempty) (f : EdgeConfiguration → ℝ)
    (hf : ∀ T ∈ spanningTrees K, 0 < f (finiteTreeConfiguration T)) :
    0 < ∫ X, f X ∂finiteUSTMeasure K := by
  rw [integral_finiteUSTMeasure]
  exact div_pos (Finset.sum_pos hf hK) (by exact_mod_cast hK.card_pos)

lemma integral_exp_finiteUSTMeasure_pos (K : FiniteSubgraphCode)
    (hK : (spanningTrees K).Nonempty) (f : EdgeConfiguration → ℝ) :
    0 < ∫ X, Real.exp (f X) ∂finiteUSTMeasure K :=
  integral_finiteUSTMeasure_pos K hK _ (fun _ _ => Real.exp_pos _)

lemma measurable_finiteUSTMeasure : Measurable finiteUSTMeasure :=
  measurable_of_countable _

def finiteUSTKernel : ProbabilityTheory.Kernel FiniteSubgraphCode EdgeConfiguration :=
  ⟨finiteUSTMeasure, measurable_finiteUSTMeasure⟩

@[simp] lemma finiteUSTKernel_apply (K : FiniteSubgraphCode) :
    finiteUSTKernel K = finiteUSTMeasure K := rfl

instance finiteUSTKernel_isFiniteKernel : ProbabilityTheory.IsFiniteKernel finiteUSTKernel :=
  ⟨⟨1, ENNReal.one_lt_top, finiteUSTMeasure_univ_le_one⟩⟩

end Problem336

end

end OAI
