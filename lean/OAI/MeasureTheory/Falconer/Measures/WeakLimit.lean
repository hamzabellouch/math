import OAI.MeasureTheory.Falconer.Measures.DyadicMeasure
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric

namespace OAI

namespace PlanarFalconer
open Set Metric MeasureTheory Filter
open scoped ENNReal NNReal Topology

theorem compact_carried_probabilities (E : Set Plane) (hE : IsCompact E) :
    IsCompact {μ : ProbabilityMeasure Plane | (μ : Measure Plane) Eᶜ = 0} := by
  have compactBound := isCompact_setOfPred_probabilityMeasure_mass_eq_compl_isCompact_le
    (u := fun _ => 0) (K := fun _ => E) tendsto_const_nhds (fun _ => hE)
    (Or.inr monotone_const)
  simpa only [le_zero_iff, forall_const, ProbabilityMeasure.null_iff_toMeasure_null]
    using compactBound

theorem exists_carried_weak_subsequence (E : Set Plane) (hE : IsCompact E)
    (μ : ℕ → ProbabilityMeasure Plane) (hμ : ∀ K, (μ K : Measure Plane) Eᶜ = 0) :
    ∃ ζ : ProbabilityMeasure Plane, (ζ : Measure Plane) Eᶜ = 0 ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (μ ∘ φ) atTop (𝓝 ζ) :=
  (compact_carried_probabilities E hE).tendsto_subseq hμ

theorem weak_limit_ball_bound (μ : ℕ → ProbabilityMeasure Plane)
    (ζ : ProbabilityMeasure Plane) (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (hlim : Tendsto (μ ∘ φ) atTop (𝓝 ζ))
    (x : Plane) (r : ℝ) (B : ℝ≥0∞)
    (hbound : ∀ᶠ K in atTop, (μ K : Measure Plane) (ball x r) ≤ B) :
    (ζ : Measure Plane) (ball x r) ≤ B := by
  have h := ProbabilityMeasure.le_liminf_measure_open_of_tendsto hlim (G := ball x r) isOpen_ball
  apply h.trans
  have hb := hφ.tendsto_atTop.eventually hbound
  exact (liminf_le_liminf hb).trans_eq (liminf_const B)

theorem frostman_of_eventual_ball_bounds (E : Set Plane) (hE : IsCompact E)
    (μ : ℕ → ProbabilityMeasure Plane) (hμ : ∀ K, (μ K : Measure Plane) Eᶜ = 0)
    (s C : ℝ)
    (hbound : ∀ x : Plane, ∀ r > 0, ∀ᶠ K in atTop,
      (μ K : Measure Plane) (ball x r) ≤ ENNReal.ofReal (C*r^s)) :
    ∃ ζ : ProbabilityMeasure Plane, (ζ : Measure Plane) Eᶜ = 0 ∧
      ∀ x : Plane, ∀ r > 0,
        (ζ : Measure Plane) (ball x r) ≤ ENNReal.ofReal (C*r^s) := by
  obtain ⟨ζ,hζ,φ,hφ,hlim⟩ := exists_carried_weak_subsequence E hE μ hμ
  exact ⟨ζ,hζ,fun x r hr => weak_limit_ball_bound μ ζ φ hφ hlim x r _ (hbound x r hr)⟩

end PlanarFalconer

end OAI
