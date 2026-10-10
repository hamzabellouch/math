import Mathlib
import OAI.Analysis.RieszRectifiability.Limits.FiniteMeasureSequentialCompactness
import OAI.Analysis.RieszRectifiability.Limits.CompactnessUnweighting

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal

theorem le_compactnessUnweightedMeasure {d : ℕ} (n : ℕ) (ν : Measure (Ambient d)) :
    ν ≤ compactnessUnweightedMeasure n ν := by
  have h : ν.withDensity 1 ≤ ν.withDensity (fun x => ENNReal.ofReal ((compactnessWeight n x)⁻¹)) := by
    apply withDensity_mono
    exact Eventually.of_forall (fun x => by
      change (1 : ℝ≥0∞) ≤ ENNReal.ofReal ((compactnessWeight n x)⁻¹)
      rw [← ENNReal.ofReal_one]
      apply ENNReal.ofReal_le_ofReal
      rw [compactnessWeight, inv_inv]
      exact one_le_pow₀ (by linarith [norm_nonneg x]))
  simpa only [withDensity_one, compactnessUnweightedMeasure] using! h

theorem compactnessUnweightedMeasure_ne_zero {d : ℕ} (n : ℕ)
    (ν : FiniteMeasure (Ambient d)) (hν : ν ≠ 0) :
    compactnessUnweightedMeasure n (ν : Measure (Ambient d)) ≠ 0 := by
  intro hzero
  have h : (ν : Measure (Ambient d)) = 0 := by
    apply le_antisymm _ bot_le
    simpa only [hzero] using! le_compactnessUnweightedMeasure n (ν : Measure (Ambient d))
  apply hν
  apply FiniteMeasure.toMeasure_injective
  exact h

theorem exists_original_measure_compact_subsequence {d : ℕ} (n : ℕ)
    (μ : ℕ → Measure (Ambient d)) [∀ j, IsFiniteMeasureOnCompacts (μ j)]
    (C c : ℝ) (hc : 0 < c) (hg : ∀ j, GlobalUpperGrowth n C (μ j))
    (hm : ∀ j, c ≤ (μ j).real (ball (0 : Ambient d) 1)) :
    ∃ ρ : ℕ → ℕ, StrictMono ρ ∧ ∃ ν : Measure (Ambient d),
      IsFiniteMeasureOnCompacts ν ∧ ν ≠ 0 ∧ CompactTestConvergence (fun j => μ (ρ j)) ν := by
  let μw : ℕ → FiniteMeasure (Ambient d) := fun j => compactnessFiniteMeasure n (μ j) C (hg j)
  let a : ℝ := c * (2 : ℝ)⁻¹ ^ (n + 1)
  have ha : 0 < a := by dsimp only [a]; positivity
  have hC : 0 ≤ C := (hg 0).1
  have hmass : ∀ j, a ≤ ((μw j).mass : ℝ) ∧ ((μw j).mass : ℝ) ≤ 3 * C * 2 ^ n := by
    intro j
    exact ⟨compactnessFiniteMeasure_mass_lower n (μ j) C c (hg j) (hm j),
      compactnessFiniteMeasure_mass_bound n (μ j) C (hg j)⟩
  have htail : ∀ j R, 0 < R → ((μw j) (closedBall (0 : Ambient d) R)ᶜ : ℝ) ≤
      (2 * C * 2 ^ n) / R := by
    intro j R hR
    calc
      _ ≤ 2 * (C * 2 ^ n / R) := compactnessFiniteMeasure_tail_bound n (μ j) C (hg j) R hR
      _ = _ := by ring
  obtain ⟨ρ, hρ, νw, hweak, hlow, _hupp⟩ := exists_finite_measure_subsequence μw
    a (3 * C * 2 ^ n) (2 * C * 2 ^ n) ha (by positivity) hmass htail
  have hνw : νw ≠ 0 := by
    apply νw.mass_nonzero_iff.mp
    intro hz
    rw [hz, NNReal.coe_zero] at hlow
    exact (not_le_of_gt ha) hlow
  refine ⟨ρ, hρ, compactnessUnweightedMeasure n (νw : Measure (Ambient d)),
    compactnessUnweightedMeasure_locally_finite n _, compactnessUnweightedMeasure_ne_zero n νw hνw, ?_⟩
  exact compactness_weighted_limit_gives_original_limit n (fun j => μ (ρ j)) C
    (fun j => hg (ρ j)) νw hweak

end

end RieszRectifiability

end OAI
