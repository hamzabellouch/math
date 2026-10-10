import Mathlib
import OAI.Probability.CriticalPercolation.Gluing.PredictionFailure

namespace OAI

section
section
noncomputable section
open Set Function MeasureTheory ProbabilityTheory
open scoped Classical ENNReal

namespace CriticalPercolation.BernoulliProduct
variable {E : Type*}

lemma blockProbability_eq_pinnedLaw (q : E → unitInterval) (I σ : Set E)
    (A : Set (Set E)) (hA : MeasurableSet A) :
    blockProbability q I A σ=law (pinnedParameters q I σ) A := by
  rw [← forceOn_map_law,Measure.map_apply (measurable_forceOn I σ) hA]
  rfl

def predictionFailure (q : E → unitInterval) (F : Set E)
    (A C D : Set (Set E)) (δ : ℝ) : Set (Set E) :=
  Aᶜ ∪ (A∩{σ | (blockProbability q F C σ).toReal<1-δ}) ∪
    (A∩{σ | (blockProbability q F D σ).toReal<1-δ})

lemma measurableSet_predictionFailure (q : E → unitInterval) (F : Set E)
    (A C D : Set (Set E)) (hA : MeasurableSet[blockSigma F] A)
    (hC : MeasurableSet C) (hD : MeasurableSet D) (δ : ℝ) :
    MeasurableSet[blockSigma F] (predictionFailure q F A C D δ) := by
  exact (hA.compl.union (hA.inter (measurableSet_lt
    (measurable_blockProbability q F C hC).ennreal_toReal measurable_const))).union
    (hA.inter (measurableSet_lt
      (measurable_blockProbability q F D hD).ennreal_toReal measurable_const))

theorem pinned_prediction_failure (q : E → unitInterval) (I F σ : Set E)
    (hIF : I⊆F) (A C D : Set (Set E))
    (hA : MeasurableSet[blockSigma F] A) (hC : MeasurableSet C) (hD : MeasurableSet D)
    (δ a : ℝ) (hδ : 0<δ)
    (hin : 1-δ ≤ (blockProbability q I A σ).toReal)
    (hCfail : (blockProbability q I (A\C) σ).toReal ≤ a)
    (hDfail : (blockProbability q I (A\D) σ).toReal ≤ a) :
    (blockProbability q I (predictionFailure q F A C D δ) σ).toReal ≤ δ+2*a/δ := by
  have hma := (blockSigma_le F) _ hA
  rw [blockProbability_eq_pinnedLaw q I σ A hma] at hin
  rw [blockProbability_eq_pinnedLaw q I σ (A\C) (hma.diff hC)] at hCfail
  rw [blockProbability_eq_pinnedLaw q I σ (A\D) (hma.diff hD)] at hDfail
  have hh := two_prediction_failure (pinnedParameters q I σ) F A C D hA hC hD δ a hδ
    hin hCfail hDfail
  simp_rw [blockProbability_pin_smaller q I F σ hIF C hC,
    blockProbability_pin_smaller q I F σ hIF D hD] at hh
  rw [blockProbability_eq_pinnedLaw q I σ _
    ((blockSigma_le F) _ (measurableSet_predictionFailure q F A C D hA hC hD δ))]
  exact hh

lemma predictionFailure_pin_smaller (q : E → unitInterval) (I F σ : Set E)
    (hIF : I⊆F) (A C D : Set (Set E)) (hC : MeasurableSet C)
    (hD : MeasurableSet D) (δ : ℝ) :
    predictionFailure (pinnedParameters q I σ) F A C D δ=predictionFailure q F A C D δ := by
  unfold predictionFailure
  simp_rw [blockProbability_pin_smaller q I F σ hIF C hC,
    blockProbability_pin_smaller q I F σ hIF D hD]

end CriticalPercolation.BernoulliProduct
end
end
end

end OAI
