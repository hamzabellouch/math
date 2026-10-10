import Mathlib
import OAI.Probability.Ballisticity.Geometry.PairHeight
import OAI.Probability.Ballisticity.Estimates.RawPair

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience
lemma bufferStageRetainedLaw_success {d : ℕ} (e f : Direction d)
    (a z₀ r ε α g : ℝ) (π : Environment d → SupportedPairMeasures (PairAtHeight (realPosition (step e)) a))
    {H : ℕ} (hH : 0 < H) (ω : Environment d) (κ : ℝ≥0)
    (hE : BufferStageEvent (realPosition (step e)) f H z₀ r ε α g (π ω).val ω) :
    bufferStageRetainedLaw e f a z₀ r ε α g π H ω κ =
      retainedPairLaw (realPosition (step e)) f H (z₀+(1+α)*r) (π ω).val ω := by
  have ht := (bufferStageEvent_iff_last_tests (realPosition (step e)) f a z₀ r ε α g π hH ω).mp hE
  simp only [bufferStageRetainedLaw,ite_eq_right (not_lt_of_ge ht.1),ite_eq_left ht.2]

lemma bufferStageRetainedLaw_failure_support {d : ℕ} (e f : Direction d)
    (a z₀ r ε α g : ℝ) (π : Environment d → SupportedPairMeasures (PairAtHeight (realPosition (step e)) a))
    {H : ℕ} (hH : 0 < H) (ω : Environment d) (κ : ℝ≥0)
    (hE : ¬ BufferStageEvent (realPosition (step e)) f H z₀ r ε α g (π ω).val ω) :
    ∀ᵐ y ∂bufferStageRetainedLaw e f a z₀ r ε α g π H ω κ,
      z₀+(1-ε)*r ≤ signedCoordinate f (y.2-y.1) := by
  unfold bufferStageRetainedLaw
  dsimp only
  split
  · exact upwardRetainedLaw_support _ _ _ _ _ _ _
  · rename_i hp
    have hn : ¬ ENNReal.ofReal g ≤ pairKernelMass (realPosition (step e)) f H
        (z₀+(1+α)*r) (π ω).val ω := by
      intro hh
      apply hE
      exact (bufferStageEvent_iff_last_tests (realPosition (step e)) f a z₀ r ε α g π hH ω).mpr
        ⟨le_of_not_gt hp,hh⟩
    simp only [ite_eq_right hn]
    exact retainedPairLaw_support _ _ _ _ _ _

lemma bufferStageRetainedLaw_height {d : ℕ} (e f : Direction d)
    (a z₀ r ε α g : ℝ) (π : Environment d → SupportedPairMeasures (PairAtHeight (realPosition (step e)) a))
    {H : ℕ} (hH : 0 < H) (ω : Environment d) {κ : ℝ≥0}
    (hκ : ∀ y, κ ≤ (ω y).1 e) :
    ∀ᵐ y ∂bufferStageRetainedLaw e f a z₀ r ε α g π H ω κ,
      y ∈ PairAtHeight (realPosition (step e))
        (a+bufferFirstFailure (realPosition (step e)) f a (z₀+(1-ε)*r) g π H ω) := by
  apply (Measure.absolutelyContinuous_of_le
    (bufferStageRetainedLaw_le e f a z₀ r ε α g π hH ω hκ)).ae_le
  apply rawPairMixture_height
  exact ae_iff.mpr (π ω).property

lemma bufferStageRetainedLaw_probability {d : ℕ} (e f : Direction d)
    (a z₀ r ε α g : ℝ) (π : Environment d → SupportedPairMeasures (PairAtHeight (realPosition (step e)) a))
    {H : ℕ} (hH : 0 < H) (ω : Environment d) {κ : ℝ≥0}
    (hκ : ∀ y, κ ≤ (ω y).1 e) (hκpos : 0 < κ)
    (hκ1 : κ ≤ 1) (hg : 0 < g) (hg1 : g ≤ 1) (hr : 0 ≤ r) (hε : 0 ≤ ε)
    [IsProbabilityMeasure (π ω).val]
    (hgap : ∀ᵐ x ∂(π ω).val, z₀+r ≤ signedCoordinate f (x.2-x.1)) :
    IsProbabilityMeasure (normalizedMeasure (bufferStageRetainedLaw e f a z₀ r ε α g π H ω κ)) := by
  have hle := bufferStageRetainedLaw_le e f a z₀ r ε α g π hH ω hκ
  have hl := bufferStageRetainedLaw_mass_lower e f a z₀ r ε α g π hH ω κ hκ1 hg1 hr hε hgap
  have hm : bufferStageRetainedLaw e f a z₀ r ε α g π H ω κ Set.univ ≤ 1 :=
    (hle _).trans (rawPairMixture_le_one _ _ _ _)
  let : IsFiniteMeasure (bufferStageRetainedLaw e f a z₀ r ε α g π H ω κ) :=
    ⟨lt_of_le_of_lt hm ENNReal.one_lt_top⟩
  apply normalizedMeasure_probability
  apply ne_of_gt (lt_of_lt_of_le _ hl)
  have hκ0 : (κ : ℝ≥0∞) ≠ 0 := by exact_mod_cast hκpos.ne'
  exact ENNReal.mul_pos (pow_ne_zero 2 hκ0) (ENNReal.ofReal_pos.mpr hg).ne'
end DirectionalTransience

end

end

end OAI
