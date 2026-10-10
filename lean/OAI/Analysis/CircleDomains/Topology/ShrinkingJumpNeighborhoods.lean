import OAI.Analysis.CircleDomains.Selection.ShrinkingJumpTolls
import Mathlib.Topology.MetricSpace.Thickening

namespace OAI

/-! Metric thickenings of shrinking jump disks converge to the containing
dust point, so the abstract toll estimate applies to the actual jump costs. -/

open Set Filter Metric
open scoped Topology ENNReal

noncomputable section

namespace CircleDomainRigidity

variable {X : Type*} [MetricSpace X]

theorem shrinking_thickenings {s : X} {V : ℕ → Set X} {r τ : ℕ → ℝ}
    (hV : ∀ j, V j ⊆ ball s (r j)) (hr : Tendsto r atTop (𝓝 0))
    (hτ : Tendsto τ atTop (𝓝 0)) :
    ∀ W ∈ 𝓝 s, ∀ᶠ j in atTop, thickening (τ j) (V j) ⊆ W := by
  intro W hW
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hW
  have hsmall : ∀ᶠ j in atTop, r j + τ j < ε := by
    have hsum : Tendsto (fun j => r j + τ j) atTop (𝓝 0) := by simpa using hr.add hτ
    exact hsum.eventually (gt_mem_nhds hε)
  filter_upwards [hsmall] with j hj
  intro x hx
  obtain ⟨y, hy, hxy⟩ := mem_thickening_iff.mp hx
  apply hball
  have hy' : dist y s < r j := hV j hy
  change dist x s < ε
  exact (dist_triangle x y s).trans_lt ((add_lt_add hxy hy').trans_eq (add_comm _ _)) |>.trans hj

theorem shrinking_thickening_toll_limsup {m : X → ℝ≥0∞}
    (hm : (∑' x, m x ^ 2) ≠ ∞) {s : X} {V : ℕ → Set X} {r τ : ℕ → ℝ}
    (hV : ∀ j, V j ⊆ ball s (r j)) (hr : Tendsto r atTop (𝓝 0))
    (hτ : Tendsto τ atTop (𝓝 0)) {ρ : ℕ → ℝ≥0∞} (hρ : Tendsto ρ atTop (𝓝 0)) :
    limsup (fun j => max (ρ j) (neighborhoodTollSup m (thickening (τ j) (V j)))) atTop ≤ m s :=
  shrinking_jump_toll_limsup hm (shrinking_thickenings hV hr hτ) hρ

end CircleDomainRigidity

end

end OAI
