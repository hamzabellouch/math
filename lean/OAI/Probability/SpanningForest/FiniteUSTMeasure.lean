import OAI.Probability.SpanningForest.Definitions

namespace OAI

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal

namespace Problem336

attribute [local instance] Classical.propDecidable

def finiteTreeConfiguration (T : Finset (ℕ × ℕ)) : EdgeConfiguration :=
  fun e => decide (e.1 ∈ T)

def edgeCylinder (A B : Finset EdgeCode) : Set EdgeConfiguration :=
  {X | (∀ e ∈ A, X e = true) ∧ (∀ e ∈ B, X e = false)}

lemma measurableSet_edgeCylinder (A B : Finset EdgeCode) :
    MeasurableSet (edgeCylinder A B) := by
  unfold edgeCylinder
  convert (A.measurableSet_biInter fun e _ =>
    (measurable_pi_apply e) (measurableSet_singleton true)).inter
    (B.measurableSet_biInter fun e _ =>
    (measurable_pi_apply e) (measurableSet_singleton false)) using 1
  ext X
  simp

def finiteUSTMeasure (K : FiniteSubgraphCode) : Measure EdgeConfiguration :=
  (↑(spanningTrees K).card : ℝ≥0∞)⁻¹ •
    ∑ T ∈ spanningTrees K, Measure.dirac (finiteTreeConfiguration T)

lemma finiteUSTMeasure_apply (K : FiniteSubgraphCode)
    (s : Set EdgeConfiguration) (hs : MeasurableSet s) :
    finiteUSTMeasure K s =
      (↑((spanningTrees K).filter (fun T => finiteTreeConfiguration T ∈ s)).card : ℝ≥0∞) /
        (↑(spanningTrees K).card : ℝ≥0∞) := by
  classical
  simp only [finiteUSTMeasure, Measure.smul_apply, smul_eq_mul,
    Measure.finsetSum_apply, Measure.dirac_apply' _ hs, Set.indicator_apply,
    Pi.one_apply]
  rw [ENNReal.div_eq_inv_mul]
  congr 1
  simp

lemma finiteUSTMeasure_edgeCylinder (K : FiniteSubgraphCode) (A B : Finset EdgeCode) :
    finiteUSTMeasure K (edgeCylinder A B) = ustCylinder K A B := by
  classical
  rw [finiteUSTMeasure_apply K _ (measurableSet_edgeCylinder A B)]
  simp only [ustCylinder, edgeCylinder, Set.mem_ofPred_eq, finiteTreeConfiguration,
    decide_eq_true_eq, decide_eq_false_iff_not]
  congr 2
  apply congrArg Finset.card
  ext T
  simp

lemma finiteUSTMeasure_isProbabilityMeasure (K : FiniteSubgraphCode)
    (hK : (spanningTrees K).Nonempty) : IsProbabilityMeasure (finiteUSTMeasure K) := by
  constructor
  rw [finiteUSTMeasure_apply K Set.univ MeasurableSet.univ]
  simp only [Set.mem_univ, Finset.filter_true]
  exact ENNReal.div_self (by exact_mod_cast Finset.card_ne_zero.mpr hK) (by simp)

lemma finiteUSTMeasure_eq_zero (K : FiniteSubgraphCode)
    (hK : spanningTrees K = ∅) : finiteUSTMeasure K = 0 := by
  simp [finiteUSTMeasure, hK]

lemma finiteUSTMeasure_univ_le_one (K : FiniteSubgraphCode) :
    finiteUSTMeasure K Set.univ ≤ 1 := by
  classical
  by_cases hK : (spanningTrees K).Nonempty
  · let := finiteUSTMeasure_isProbabilityMeasure K hK
    simp
  · rw [finiteUSTMeasure_eq_zero K (Finset.not_nonempty_iff_eq_empty.mp hK)]
    simp

instance finiteUSTMeasure_isFiniteMeasure (K : FiniteSubgraphCode) :
    IsFiniteMeasure (finiteUSTMeasure K) :=
  ⟨lt_of_le_of_lt (finiteUSTMeasure_univ_le_one K) ENNReal.one_lt_top⟩

lemma finiteUSTMeasure_concentrated (K : FiniteSubgraphCode) :
    ∀ᵐ X ∂finiteUSTMeasure K,
      ∃ T ∈ spanningTrees K, finiteTreeConfiguration T = X := by
  classical
  rw [ae_iff]
  let S : Finset EdgeConfiguration := (spanningTrees K).image finiteTreeConfiguration
  have hS : MeasurableSet (S : Set EdgeConfiguration) := S.finite_toSet.measurableSet
  have hset : {X | ¬ ∃ T ∈ spanningTrees K, finiteTreeConfiguration T = X} =
      (S : Set EdgeConfiguration)ᶜ := by
    ext X
    simp [S]
  rw [hset, finiteUSTMeasure_apply K _ hS.compl]
  simp
  intro T hT
  exact Finset.mem_image.mpr ⟨T, hT, rfl⟩

end Problem336

end

end OAI
