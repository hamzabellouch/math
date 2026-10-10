import Mathlib
import OAI.Probability.Ballisticity.Entropy.OccupationEntropy2

namespace OAI

section

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal Classical BigOperators
namespace DirectionalTransience

lemma actualCurrentWindow_restricted_law {d : ℕ} (e : Direction d)
    (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (Q : Measure (Environment d)) [IsFiniteMeasure Q]
    (t : Environment d → ℤ → ℕ) (ht : ∀ i, Measurable fun ω => t ω i)
    (i : ℤ) (m N : ℕ)
    (hi : ∀ n : ℕ, MeasurableSet[rowSigma (BelowHeight (realPosition (step e)) n)] {ω | t ω i=n})
    (him : ∀ n : ℕ, MeasurableSet[rowSigma (BelowHeight (realPosition (step e)) n)] {ω | t ω (i+m)=n})
    (filler : Environment d) :
    ((rawCurrentWindow e ν Q (fun ω => t ω i) (fun ω => t ω (i+m)) (ht i) filler).restrict
      {p | p.1.1<N}).map (rawCurrentProjection e) =
      ((episodeInputLaw e ν Q t ht).restrict {X | t X.1.1 i<N}).map
        (actualCurrentWindow e t i m) := by
  unfold rawCurrentWindow
  rw [← episodeInputLaw_current e ν Q t ht i m]
  rw [Measure.map_map (rawCurrentWindow_measurable e _ _ hi him filler)
    (currentInput_measurable e i m)]
  have hf := (rawCurrentWindow_measurable e _ _ hi him filler).comp (currentInput_measurable e i m)
  have hA : MeasurableSet {p : RawCurrentData e × LocalUpperField e | p.1.1<N} :=
    measurableSet_lt (measurable_fst.comp measurable_fst) measurable_const
  rw [Measure.restrict_map hf hA]
  rw [Measure.map_map (rawCurrentProjection_measurable e) hf]
  congr 1
  funext X
  exact actualCurrentWindow_raw e t i m hi filler X

lemma rawCurrentOccupation_projected {d : ℕ} (e : Direction d)
    (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (Q : Measure (Environment d)) [IsFiniteMeasure Q]
    (t : Environment d → ℤ → ℕ) (ht : ∀ i, Measurable fun ω => t ω i)
    (hst : ∀ (i : ℤ) (n : ℕ), MeasurableSet[rowSigma (BelowHeight (realPosition (step e)) n)] {ω | t ω i=n})
    (filler : Environment d) (N m : ℕ) :
    (rawCurrentOccupation e ν Q (fun i ω => t ω i) (fun i => ht i) filler N m).map
      (rawCurrentProjection e) =
      ∑ i ∈ Finset.range N, ((episodeInputLaw e ν Q t ht).restrict {X | t X.1.1 i<N}).map
        (actualCurrentWindow e t i m) := by
  unfold rawCurrentOccupation Entropy.activeSum
  rw [Measure.map_finset_sum (rawCurrentProjection_measurable e).aemeasurable]
  apply Finset.sum_congr rfl
  intro i _
  simpa only [Nat.cast_add] using actualCurrentWindow_restricted_law e ν Q t ht i m N
    (hst i) (hst (i+m)) filler

end DirectionalTransience

end

end OAI
