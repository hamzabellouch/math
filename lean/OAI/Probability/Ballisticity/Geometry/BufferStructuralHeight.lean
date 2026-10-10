import Mathlib
import OAI.Probability.Ballisticity.Estimates.BufferStagePacket
import OAI.Probability.Ballisticity.Walk.BufferNormalizedRows

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience
lemma bufferStageRetainedLaw_height_unconditional {d : ℕ} (e f : Direction d)
    (a z₀ r ε α g : ℝ) (π : Environment d → SupportedPairMeasures (PairAtHeight (realPosition (step e)) a))
    {H : ℕ} (hH : 0 < H) (ω : Environment d) (κ : ℝ≥0) :
    ∀ᵐ y ∂bufferStageRetainedLaw e f a z₀ r ε α g π H ω κ,
      y ∈ PairAtHeight (realPosition (step e))
        (a+bufferFirstFailure (realPosition (step e)) f a (z₀+(1-ε)*r) g π H ω) := by
  let ℓ := realPosition (step e)
  let z := z₀+(1-ε)*r
  let j := bufferFirstFailure ℓ f a z g π H ω
  have hπ : ∀ᵐ x ∂(π ω).val, x ∈ PairAtHeight ℓ a := ae_iff.mpr (π ω).property
  have hj : 1 ≤ j := (bufferFirstFailure_bounds ℓ f a z g π hH ω).1
  unfold bufferStageRetainedLaw
  dsimp only
  split
  · have he : j-1+1=j := by omega
    simpa only [he] using upwardRetainedLaw_height e f (j-1) z ω (π ω).val κ a hπ
  · rename_i hp
    have hjH : j=H := bufferFirstFailure_eq_top_of_pass ℓ f a z g π hH ω (le_of_not_gt hp)
    change ∀ᵐ y ∂(if _ then _ else _), y ∈ PairAtHeight ℓ (a+j)
    rw [hjH]
    split <;> exact retainedPairLaw_height e f H _ ω (π ω).val a hπ

noncomputable def bufferStageStoppedProbability {d : ℕ} (e f : Direction d)
    (a z₀ r ε α g : ℝ) (π : Environment d → SupportedPairMeasures (PairAtHeight (realPosition (step e)) a))
    (H : ℕ) (hH : 0 < H) (κ : ℝ≥0) (k : ℕ) (ω : Environment d) :
    SupportedPairMeasures (PairAtHeight (realPosition (step e)) (a+k)) :=
  ⟨if bufferFirstFailure (realPosition (step e)) f a (z₀+(1-ε)*r) g π H ω = k
    then normalizedMeasure (bufferStageRetainedLaw e f a z₀ r ε α g π H ω κ) else 0, by
      split
      · rename_i hk
        apply ae_iff.mp
        apply Measure.ae_smul_measure
        simpa only [hk] using bufferStageRetainedLaw_height_unconditional e f a z₀ r ε α g π hH ω κ
      · simp⟩

lemma bufferStageStoppedProbability_rows {d : ℕ} (e f : Direction d)
    (a z₀ r ε α g : ℝ) (π : Environment d → SupportedPairMeasures (PairAtHeight (realPosition (step e)) a))
    (hπ : @Measurable _ _ (rowSigma (BelowHeight (realPosition (step e)) a)) _ π)
    (H : ℕ) (hH : 0 < H) (κ : ℝ≥0) (k : ℕ) :
    @Measurable _ _ (rowSigma (BelowHeight (realPosition (step e)) (a+k))) _
      (bufferStageStoppedProbability e f a z₀ r ε α g π H hH κ k) := by
  exact (bufferStage_normalized_stopped_rows e f a z₀ r ε α g π hπ hH κ k).subtype_mk

lemma bufferStageStoppedProbability_gap {d : ℕ} (e f : Direction d)
    (a z₀ r ε α g : ℝ) (π : Environment d → SupportedPairMeasures (PairAtHeight (realPosition (step e)) a))
    (H : ℕ) (hH : 0 < H) (κ : ℝ≥0) (k : ℕ) (ω : Environment d) :
    ∀ᵐ y ∂(bufferStageStoppedProbability e f a z₀ r ε α g π H hH κ k ω).val,
      z₀+(if BufferStageEvent (realPosition (step e)) f H z₀ r ε α g (π ω).val ω
        then (1+α)*r else (1-ε)*r) ≤ signedCoordinate f (y.2-y.1) := by
  by_cases hk : bufferFirstFailure (realPosition (step e)) f a (z₀+(1-ε)*r) g π H ω = k
  · simp only [bufferStageStoppedProbability,ite_eq_left hk]
    apply Measure.ae_smul_measure
    by_cases hE : BufferStageEvent (realPosition (step e)) f H z₀ r ε α g (π ω).val ω
    · rw [ite_eq_left hE,bufferStageRetainedLaw_success e f a z₀ r ε α g π hH ω κ hE]
      exact retainedPairLaw_support _ _ _ _ _ _
    · rw [ite_eq_right hE]
      exact bufferStageRetainedLaw_failure_support e f a z₀ r ε α g π hH ω κ hE
  · simp [bufferStageStoppedProbability,ite_eq_right hk]
end DirectionalTransience

end

end

end OAI
