import Mathlib
import OAI.Probability.Ballisticity.Estimates.RawPairRetention
import OAI.Probability.Ballisticity.Coupling.FreshWeightedTest

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

lemma fresh_rows_weighted_test_lower {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    {S T : Set (Lattice d)} (hST : Disjoint S T)
    (G : Set (Environment d × Environment d))
    (hG : @MeasurableSet (Environment d × Environment d)
      (MeasurableSpace.prod (rowSigma S) (rowSigma T)) G)
    (A : Set (Environment d)) (hA : MeasurableSet[rowSigma S] A)
    (w : Environment d → ℝ≥0∞) (hw : @Measurable _ _ (rowSigma S) _ w)
    (c : ℝ≥0∞) (hbound : ∀ η ∈ A, c ≤ environmentLaw ν {ω | (η,ω) ∈ G}) :
    c*(∫⁻ ω in A, w ω ∂environmentLaw ν) ≤
      ∫⁻ ω in {ω | ω ∈ A ∧ (ω,ω) ∈ G}, w ω ∂environmentLaw ν := by
  have hU : @Measurable (Environment d) (Environment d) inferInstance (rowSigma S) id :=
    measurable_id.mono le_rfl (rowSigma_le S)
  have hV : @Measurable (Environment d) (Environment d) inferInstance (rowSigma T) id :=
    measurable_id.mono le_rfl (rowSigma_le T)
  have hb (η : Environment d) (hη : η ∈ A) :
      c ≤ (@Measure.map (Environment d) (Environment d) inferInstance (rowSigma T) id (environmentLaw ν))
        {ω | (η,ω) ∈ G} := by
    have he : {ω | (η,ω) ∈ G} = Prod.mk η ⁻¹' G := rfl
    rw [he,Measure.map_apply hV (hG.preimage measurable_prodMk_left)]
    exact hbound η hη
  exact @independent_random_test_weighted_lower (Environment d) (Environment d) (Environment d)
    inferInstance (rowSigma S) (rowSigma T) (environmentLaw ν) inferInstance
    id id hU hV
    (@indepFun_of_disjoint_rows d (Environment d) (Environment d) (rowSigma S) (rowSigma T)
      ν _ S T hST id id measurable_id measurable_id) A hA G hG w hw c hb

lemma fresh_buffer_weighted_test {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) (f : Direction d) {H : ℕ} (hH : 0 < H) (z₀ r ε a g : ℝ)
    (C : Set (Lattice d × Lattice d)) {S T : Set (Lattice d)} (hST : Disjoint S T)
    (hC : ∀ x ∈ C, Strip ℓ x.1 H ⊆ T ∧ Strip ℓ x.2 H ⊆ T)
    (π : Environment d → SupportedPairMeasures C)
    (hπ : @Measurable _ _ (rowSigma S) _ π)
    (A : Set (Environment d)) (hA : MeasurableSet[rowSigma S] A)
    (w : Environment d → ℝ≥0∞) (hw : @Measurable _ _ (rowSigma S) _ w)
    (c : ℝ≥0∞)
    (hbound : ∀ η ∈ A, c ≤ environmentLaw ν
      {ω | BufferStageEvent ℓ f H z₀ r ε a g (π η).val ω}) :
    c*(∫⁻ ω in A, w ω ∂environmentLaw ν) ≤
      ∫⁻ ω in {ω | ω ∈ A ∧ BufferStageEvent ℓ f H z₀ r ε a g (π ω).val ω},
        w ω ∂environmentLaw ν := by
  let G : Set (Environment d × Environment d) :=
    {p | BufferStageEvent ℓ f H z₀ r ε a g (π p.1).val p.2}
  have hG : @MeasurableSet (Environment d × Environment d)
      (MeasurableSpace.prod (rowSigma S) (rowSigma T)) G :=
    (measurableSet_bufferStageEvent_rows ℓ f hH z₀ r ε a g C T hC).preimage
      ((hπ.comp measurable_fst).prodMk measurable_snd)
  exact fresh_rows_weighted_test_lower ν hST G hG A hA w hw c hbound
end DirectionalTransience

end

end

end OAI
