import Mathlib
import OAI.Probability.Ballisticity.Entropy.StoppedWindowEntropy
import OAI.Probability.Ballisticity.Stationary.EpisodeEntropyTelescoping

namespace OAI

section

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal Classical BigOperators
namespace DirectionalTransience

noncomputable def layerInformation {d : ℕ} (e : Direction d)
    (ν : Measure (Row d)) (Q : Measure (Environment d))
    (τ : Environment d → ℕ) (filler : Environment d) : ℝ≥0∞ :=
  klDiv (Q.map (stoppedObservation (fun n => BelowHeight (realPosition (step e)) n) τ filler))
    ((environmentLaw ν).map
      (stoppedObservation (fun n => BelowHeight (realPosition (step e)) n) τ filler))

noncomputable def ownedWindowEntropy {d : ℕ} (e : Direction d)
    (ν : Measure (Row d)) (Q : Measure (Environment d))
    (τ σ : Environment d → ℕ) (filler : Environment d) : ℝ≥0∞ :=
  klDiv (stoppedWindowLaw e ν Q τ σ filler)
    ((Q.map (stoppedObservation (fun n => BelowHeight (realPosition (step e)) n) τ filler)).prod
      (Measure.infinitePi (fun _ : ℕ × HorizontalSpace e => ν)))

lemma layerInformation_le {d : ℕ} (e : Direction d)
    (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (Q : Measure (Environment d)) [IsFiniteMeasure Q]
    (τ : Environment d → ℕ)
    (hτ : ∀ n : ℕ, MeasurableSet[rowSigma (BelowHeight (realPosition (step e)) n)] {ω | τ ω=n})
    (filler : Environment d) : layerInformation e ν Q τ filler ≤ klDiv Q (environmentLaw ν) :=
  klDiv_map_le Q (environmentLaw ν) (stoppedObservation_measurable _ τ hτ filler)

lemma ownedWindowEntropy_finite_budget {d : ℕ} (e : Direction d)
    (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (Q : Measure (Environment d)) [IsProbabilityMeasure Q]
    (hfin : klDiv Q (environmentLaw ν) ≠ ∞)
    (τ σ : Environment d → ℕ) (hτσ : ∀ ω, τ ω≤σ ω)
    (hτ : ∀ n : ℕ, MeasurableSet[rowSigma (BelowHeight (realPosition (step e)) n)] {ω | τ ω=n})
    (hσ : ∀ n : ℕ, MeasurableSet[rowSigma (BelowHeight (realPosition (step e)) n)] {ω | σ ω=n})
    (filler : Environment d) :
    ownedWindowEntropy e ν Q τ σ filler ≠ ∞ ∧
    (ownedWindowEntropy e ν Q τ σ filler).toReal ≤
      (layerInformation e ν Q σ filler).toReal - (layerInformation e ν Q τ filler).toReal := by
  have h : layerInformation e ν Q τ filler + ownedWindowEntropy e ν Q τ σ filler ≤
      layerInformation e ν Q σ filler :=
    actual_stopped_window_entropy_increment e ν Q τ σ hτσ hτ hσ filler
  have hfσ : layerInformation e ν Q σ filler ≠ ∞ :=
    ne_top_of_le_ne_top hfin (layerInformation_le e ν Q σ hσ filler)
  have hf := ENNReal.add_ne_top.mp (ne_top_of_le_ne_top hfσ h)
  refine ⟨hf.2, ?_⟩
  have hr := ENNReal.toReal_mono hfσ h
  rw [ENNReal.toReal_add hf.1 hf.2] at hr
  linarith

theorem sum_actual_stopped_window_entropy {d : ℕ} (e : Direction d)
    (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (Q : Measure (Environment d)) [IsProbabilityMeasure Q]
    (hfin : klDiv Q (environmentLaw ν) ≠ ∞)
    (t : ℕ → Environment d → ℕ)
    (ht : ∀ i n : ℕ, MeasurableSet[rowSigma (BelowHeight (realPosition (step e)) n)]
      {ω | t i ω=n})
    (hmono : ∀ ω, Monotone (fun i => t i ω))
    (filler : Environment d) (N m : ℕ) :
    (∑ i ∈ Finset.range N, (ownedWindowEntropy e ν Q (t i) (t (i+m)) filler).toReal) ≤
      (m:ℝ)*(klDiv Q (environmentLaw ν)).toReal := by
  let s : ℕ → ℝ := fun i => (layerInformation e ν Q (t i) filler).toReal
  calc
    _ ≤ ∑ i ∈ Finset.range N, (s (i+m)-s i) := by
      apply Finset.sum_le_sum
      intro i _
      exact (ownedWindowEntropy_finite_budget e ν Q hfin (t i) (t (i+m))
        (fun ω => hmono ω (Nat.le_add_right i m)) (ht i) (ht (i+m)) filler).2
    _ ≤ _ := StoppedWindow.sum_window_increments_le s N m _
      (fun _ => ENNReal.toReal_nonneg)
      (fun i => ENNReal.toReal_mono hfin (layerInformation_le e ν Q (t i) (ht i) filler))

end DirectionalTransience

end

end OAI
