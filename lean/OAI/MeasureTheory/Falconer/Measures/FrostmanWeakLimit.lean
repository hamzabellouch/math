import OAI.MeasureTheory.Falconer.Measures.StartingMeasures
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric

namespace OAI

/-! # Compact weak limits preserve the required Frostman ball bounds -/
namespace Falconer
open Set Metric MeasureTheory Filter
open scoped ENNReal Topology

theorem compact_carried_probabilities {d : ℕ} (E : Set (Space d)) (hE : IsCompact E) :
    IsCompact {μ : ProbabilityMeasure (Space d) | (μ : Measure (Space d)) Eᶜ = 0} := by
  have h := isCompact_setOfPred_probabilityMeasure_mass_eq_compl_isCompact_le
    (u := fun _ => 0) (K := fun _ => E) tendsto_const_nhds (fun _ => hE)
    (Or.inr monotone_const)
  simpa only [le_zero_iff,forall_const,ProbabilityMeasure.null_iff_toMeasure_null] using h

theorem exists_carried_weak_subsequence {d : ℕ} (E : Set (Space d)) (hE : IsCompact E)
    (μ : ℕ → ProbabilityMeasure (Space d))
    (hμ : ∀ K, (μ K : Measure (Space d)) Eᶜ = 0) :
    ∃ ν : ProbabilityMeasure (Space d), (ν : Measure (Space d)) Eᶜ = 0 ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (μ ∘ φ) atTop (𝓝 ν) :=
  (compact_carried_probabilities E hE).tendsto_subseq hμ

theorem frostman_of_eventual_ball_bounds {d : ℕ} (E : Set (Space d)) (hE : IsCompact E)
    (μ : ℕ → ProbabilityMeasure (Space d))
    (hμ : ∀ K, (μ K : Measure (Space d)) Eᶜ = 0) (s C : ℝ)
    (hbound : ∀ x : Space d, ∀ r > 0, ∀ᶠ K in atTop,
      (μ K : Measure (Space d)) (ball x r) ≤ ENNReal.ofReal (C*r^s)) :
    ∃ ν : ProbabilityMeasure (Space d), (ν : Measure (Space d)) Eᶜ = 0 ∧
      FrostmanBallBound (ν : Measure (Space d)) s C := by
  obtain ⟨ν,hν,φ,hφ,hlim⟩ := exists_carried_weak_subsequence E hE μ hμ
  refine ⟨ν,hν,fun x r hr => ?_⟩
  apply (ProbabilityMeasure.le_liminf_measure_open_of_tendsto hlim
    (G := ball x r) isOpen_ball).trans
  have hφt : Tendsto φ atTop atTop := hφ.tendsto_atTop
  have hb := hφt.eventually (hbound x r hr)
  exact (liminf_le_liminf hb).trans_eq (liminf_const _)

end Falconer

end OAI
