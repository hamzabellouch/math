import Mathlib
import OAI.Analysis.RieszRectifiability.Limits.CappedMeasureCompactness
import OAI.Analysis.RieszRectifiability.Limits.EventualGlobalLowerLimit

namespace OAI

/-!
Blowups turn capped lower growth into eventual global lower growth as their scales vanish.
Compact-test convergence then preserves these lower bounds in a tangent measure.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped ENNReal

theorem capped_blowup_lower_unit_cap {d : ℕ} (n : ℕ) (C H : ℝ) (μ : Measure (Ambient d))
    (hlower : CappedLowerGrowth n C H μ) (a : Ambient d) (s : ℝ) (hs : 0 < s) (hsH : s ≤ H) :
    CappedLowerGrowth n C 1 (blowupMeasure n μ a s) := by
  intro x hx r hr hr1
  apply CappedLowerGrowth.blowup n C H μ hlower a s hs x hx r hr
  apply hr1.trans
  exact (one_le_div hs).mpr hsH

theorem capped_blowup_eventual_global_lower {d : ℕ} (n : ℕ) (C H : ℝ) (μ : Measure (Ambient d))
    (hH : 0 < H) (hlower : CappedLowerGrowth n C H μ) (a : Ambient d)
    (s : ℕ → ℝ) (hs : ∀ j, 0 < s j) (hs0 : Tendsto s atTop (𝓝 0)) :
    ∀ r : ℝ, 0 < r → ∀ᶠ j in atTop, ∀ x ∈ (blowupMeasure n μ a (s j)).support,
      ENNReal.ofReal (r ^ n / C) ≤ blowupMeasure n μ a (s j) (ball x r) := by
  intro r hr
  have hsr : Tendsto (fun j => s j * r) atTop (𝓝 0) := by
    simpa only [zero_mul] using! hs0.mul_const r
  filter_upwards [hsr.eventually (gt_mem_nhds hH)] with j hj
  intro x hx
  apply CappedLowerGrowth.blowup n C H μ hlower a (s j) (hs j) x hx r hr
  exact (le_div_iff₀ (hs j)).mpr (by simpa only [mul_comm] using! hj.le)

theorem exists_capped_lower_tangent {d : ℕ} (n : ℕ) (C G H : ℝ)
    (μ : Measure (Ambient d)) (hC : 0 < C) (hH : 0 < H) (hg : GlobalUpperGrowth n G μ)
    (hlower : CappedLowerGrowth n C H μ) (a : Ambient d) (ha : a ∈ μ.support)
    (s : ℕ → ℝ) (hs : ∀ j, 0 < s j) (hsH : ∀ j, s j ≤ H) (hs0 : Tendsto s atTop (𝓝 0)) :
    ∃ ρ : ℕ → ℕ, StrictMono ρ ∧ ∃ ν : Measure (Ambient d),
      IsFiniteMeasureOnCompacts ν ∧ ν ≠ 0 ∧
      CompactTestConvergence (fun j => blowupMeasure n μ a (s (ρ j))) ν ∧
      GlobalUpperGrowth n (G * 2 ^ n) ν ∧ (0 : Ambient d) ∈ ν.support ∧
      ∀ x ∈ ν.support, ∀ r : ℝ, 0 < r → ENNReal.ofReal (r ^ n / (C * 4 ^ n)) ≤ ν (ball x r) := by
  let μj := fun j => blowupMeasure n μ a (s j)
  have hgj (j : ℕ) : GlobalUpperGrowth n G (μj j) := blowupMeasure_growth n μ a (s j) G (hs j) hg
  obtain ⟨ρ, hρ, ν, hfinite, hne, hlocal, hgν, _, hzeroν⟩ :=
    exists_capped_lower_measure_limit n C G 1 μj hC zero_lt_one hgj
      (fun j => capped_blowup_lower_unit_cap n C H μ hlower a (s j) (hs j) (hsH j))
      (fun j => blowupMeasure_origin_mem_support n μ a (s j) (hs j) ha)
  let := hfinite
  let : ∀ j, IsFiniteMeasureOnCompacts (μj (ρ j)) :=
    fun j => globalGrowth_finite_on_compacts G _ (hgj (ρ j))
  refine ⟨ρ, hρ, ν, hfinite, hne, hlocal, hgν, hzeroν, ?_⟩
  apply compactTestConvergence_eventual_global_lower n C (fun j => μj (ρ j)) ν hC hlocal
  exact capped_blowup_eventual_global_lower n C H μ hH hlower a
    (fun j => s (ρ j)) (fun j => hs (ρ j)) (hs0.comp hρ.tendsto_atTop)

end

end RieszRectifiability

end OAI
