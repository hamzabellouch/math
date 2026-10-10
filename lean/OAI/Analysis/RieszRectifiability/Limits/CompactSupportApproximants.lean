import Mathlib
import OAI.Analysis.RieszRectifiability.Limits.CompactLimitSupport

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology

theorem compactTestConvergence_support_approximants {d : ℕ}
    (μ : ℕ → Measure (Ambient d)) (ν : Measure (Ambient d))
    [∀ j, IsFiniteMeasureOnCompacts (μ j)] [IsFiniteMeasureOnCompacts ν]
    (hlocal : CompactTestConvergence μ ν) (b : Ambient d) (hb : b ∈ ν.support) :
    ∃ (φ : ℕ → ℕ) (a : ℕ → Ambient d),
      (∀ j, j ≤ φ j) ∧ Tendsto φ atTop atTop ∧
      (∀ j, a j ∈ (μ (φ j)).support) ∧ Tendsto a atTop (𝓝 b) := by
  have hex (k : ℕ) : ∃ j, k ≤ j ∧ ∃ x, x ∈ (μ j).support ∧
      dist x b < (1 / 2 : ℝ) ^ k := by
    obtain ⟨j, hjnear, hjlarge⟩ := ((compactTestConvergence_nearby_support μ ν hlocal b hb
      ((1 / 2 : ℝ) ^ k) (by positivity)).and (eventually_ge_atTop k)).exists
    exact ⟨j, hjlarge, hjnear⟩
  choose φ hφ a ha hd using hex
  have htop : Tendsto φ atTop atTop := tendsto_atTop_mono hφ tendsto_id
  refine ⟨φ, a, hφ, htop, ha, ?_⟩
  have hpow : Tendsto (fun k : ℕ => (1 / 2 : ℝ) ^ k) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [hpow.eventually (gt_mem_nhds hε)] with j hj
  exact (hd j).trans hj

end

end RieszRectifiability

end OAI
