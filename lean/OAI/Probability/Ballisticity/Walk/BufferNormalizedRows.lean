import Mathlib
import OAI.Probability.Ballisticity.Walk.RetentionRowsAllHeights

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

lemma normalizedMeasure_zero {α : Type*} [MeasurableSpace α] :
    normalizedMeasure (0 : Measure α) = 0 := by simp [normalizedMeasure]

lemma bufferStage_normalized_stopped_rows {d : ℕ} (e f : Direction d)
    (a z₀ r ε α g : ℝ) (π : Environment d → SupportedPairMeasures (PairAtHeight (realPosition (step e)) a))
    (hπ : @Measurable _ _ (rowSigma (BelowHeight (realPosition (step e)) a)) _ π)
    {H : ℕ} (hH : 0 < H) (κ : ℝ≥0) (k : ℕ) :
    @Measurable _ _ (rowSigma (BelowHeight (realPosition (step e)) (a+k))) _
      (fun ω => if bufferFirstFailure (realPosition (step e)) f a (z₀+(1-ε)*r) g π H ω = k
        then normalizedMeasure (bufferStageRetainedLaw e f a z₀ r ε α g π H ω κ) else 0) := by
  have hm := measurable_normalizedMeasure.comp
    (bufferStageRetainedLaw_stopped_rows e f a z₀ r ε α g π hπ hH κ k)
  convert hm using 1
  funext ω
  dsimp only [Function.comp_def]
  split <;> simp_all only [normalizedMeasure_zero]

lemma bufferStage_success_stopped_rows {d : ℕ} (e f : Direction d)
    (a z₀ r ε α g : ℝ) (π : Environment d → SupportedPairMeasures (PairAtHeight (realPosition (step e)) a))
    (hπ : @Measurable _ _ (rowSigma (BelowHeight (realPosition (step e)) a)) _ π)
    {H : ℕ} (hH : 0 < H) (k : ℕ) :
    MeasurableSet[rowSigma (BelowHeight (realPosition (step e)) (a+k))]
      {ω | bufferFirstFailure (realPosition (step e)) f a (z₀+(1-ε)*r) g π H ω = k ∧
        BufferStageEvent (realPosition (step e)) f H z₀ r ε α g (π ω).val ω} := by
  let ℓ := realPosition (step e)
  by_cases h : k=H
  · subst k
    have heq := bufferFirstFailure_eq_measurable ℓ f a (z₀+(1-ε)*r) g π hπ H H
    have hp : @Measurable _ _ (rowSigma (BelowHeight ℓ (a+H))) _ π :=
      hπ.mono (rowSigma_below_height_mono ℓ a H) le_rfl
    have hm := (measurableSet_bufferStageEvent_rows ℓ f hH z₀ r ε α g (PairAtHeight ℓ a)
      (BelowHeight ℓ (a+H)) (fun x hx => strip_subset_below_height ℓ a x hx le_rfl)).preimage
        (hp.prodMk measurable_id)
    exact heq.inter hm
  · have he : {ω | bufferFirstFailure ℓ f a (z₀+(1-ε)*r) g π H ω = k ∧
        BufferStageEvent ℓ f H z₀ r ε α g (π ω).val ω} = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      rintro ω ⟨hk,hE⟩
      have hlast := bufferFirstFailure_eq_top_of_pass ℓ f a (z₀+(1-ε)*r) g π hH ω
        ((bufferStageEvent_iff_last_tests ℓ f a z₀ r ε α g π hH ω).mp hE).1
      exact h (hk.symm.trans hlast)
    change MeasurableSet[rowSigma (BelowHeight ℓ (a+k))] _
    rw [he]
    exact @MeasurableSet.empty _ (rowSigma (BelowHeight ℓ (a+k)))
end DirectionalTransience

end

end

end OAI
