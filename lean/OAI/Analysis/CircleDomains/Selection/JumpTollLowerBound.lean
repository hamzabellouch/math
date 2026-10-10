import OAI.Analysis.CircleDomains.Topology.ShrinkingJumpNeighborhoods

namespace OAI

/-! A fixed positive neighborhood width pays the limiting dust junction.
This is the lower bound used in removal of one shrinking jump level. -/

open Set Filter Metric
open scoped Topology ENNReal

noncomputable section

namespace CircleDomainRigidity

variable {X : Type*} [MetricSpace X]

def fixedWidthJumpToll (B : Set X) (m : X → ℝ≥0∞) (ρ : ℝ≥0∞)
    (τ : ℝ) (V : Set X) : ℝ≥0∞ :=
  max ρ (neighborhoodTollSup m (B ∩ thickening τ V))

theorem eventually_mem_fixed_thickening {x : ℕ → X} {p : X} {V : ℕ → Set X}
    (hx : Tendsto x atTop (𝓝 p)) (hxV : ∀n, x n ∈ V n) {τ : ℝ} (hτ : 0 < τ) :
    ∀ᶠn in atTop, p ∈ thickening τ (V n) := by
  have hd : Tendsto (fun n => dist p (x n)) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds (x := p)).dist hx
  filter_upwards [hd.eventually (gt_mem_nhds hτ)] with n hn
  exact mem_thickening_iff.mpr ⟨x n, hxV n, hn⟩

theorem limiting_fixedWidthJumpToll_ge
    (B : Set X) (m : X → ℝ≥0∞) (ρ : ℝ≥0∞) {τ : ℝ} (hτ : 0 < τ)
    {V : ℕ → Set X} {x : ℕ → X} {p : X}
    (hx : Tendsto x atTop (𝓝 p)) (hxV : ∀n, x n ∈ V n) (hp : p ∈ B)
    {A : ℝ≥0∞} (hA : Tendsto (fun n => fixedWidthJumpToll B m ρ τ (V n)) atTop (𝓝 A)) :
    m p ≤ A := by
  apply le_of_tendsto_of_tendsto tendsto_const_nhds hA
  filter_upwards [eventually_mem_fixed_thickening hx hxV hτ] with n hn
  have hsup : m p ≤ neighborhoodTollSup m (B ∩ thickening τ (V n)) :=
    le_iSup_of_le p (le_iSup_of_le (show p ∈ B ∩ thickening τ (V n) from ⟨hp, hn⟩) le_rfl)
  exact hsup.trans (le_max_right _ _)

theorem fixedWidthJumpToll_ge_floor
    (B : Set X) (m : X → ℝ≥0∞) (ρ : ℝ≥0∞) (τ : ℝ) (V : Set X) :
    ρ ≤ fixedWidthJumpToll B m ρ τ V := le_max_left _ _

end CircleDomainRigidity

end

end OAI
