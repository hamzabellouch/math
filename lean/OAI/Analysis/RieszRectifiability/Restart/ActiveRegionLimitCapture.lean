import Mathlib
import OAI.Analysis.RieszRectifiability.Restart.ActiveRegionUniformLimit
import OAI.Analysis.RieszRectifiability.Restart.ActiveRegionSurfaceApproximation
import OAI.Analysis.RieszRectifiability.Foundations.BoundedDisplacementProperMap

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology

theorem active_region_limit_captures_region_limit {n d : ℕ}
    (μ : Measure (Ambient d)) (R : ℝ) (hR : 0 < R) (k : ℕ)
    (z : (supportLatticeNets μ R hR k).points)
    (Good : SupportCellDescendant μ R hR k z → Prop)
    (S : SupportCellDescendant μ R hR k z → AffineSubspace ℝ (Ambient d))
    (hS : ∀ i, IsAffineNPlane n (S i)) (ε : ℝ) (hε : 0 < ε)
    (hεtiny : ε ≤ 1 / 268435456) (hsmall : activeProjectionError d ε ≤ 1 / 128)
    (hfit : ∀ i, activeRegionCell Good i →
      bilateralPlaneError μ i.center (1024 * i.radius) (S i) < ε)
    (f : S (supportCellRoot μ R hR k z) → Ambient d) (hf : Continuous f)
    (htail : ∀ t (u : S (supportCellRoot μ R hR k z)),
      dist (activeRegionParameterMap μ R hR k z Good S hS t u) (f u) ≤
      ((17039360 * ε) / 63) * latticeRadius R (k + t)) :
    IsProperMap f ∧ cellRegionLimit μ R hR k z Good ⊆ Set.range f := by
  let P := S (supportCellRoot μ R hR k z)
  let B := (17039360 * ε) / 63
  have hmove : ∀ u, dist (f u) (u : Ambient d) ≤ B * latticeRadius R k := by
    intro u
    simpa only [activeRegionParameterMap, id_eq, Nat.add_zero, dist_comm] using! htail 0 u
  have hproper := isProperMap_of_bounded_displacement (P : Set (Ambient d))
    P.closed_of_finiteDimensional (hS (supportCellRoot μ R hR k z)).1 f hf
    (B * latticeRadius R k) hmove
  have hclosed : IsClosed (Set.range f) := by
    simpa only [Set.image_univ] using! hproper.isClosedMap Set.univ isClosed_univ
  refine ⟨hproper, ?_⟩
  intro x hx
  let C := 263168 * ε + B
  have happrox : ∀ t, ∃ y ∈ Set.range f, dist x y ≤ C * latticeRadius R (k + t) := by
    intro t
    obtain ⟨y, hy, hxy⟩ := activeRegionSurface_approximates_region_limit μ R hR k z Good S hS
      ε hε hεtiny hsmall hfit t x hx
    rw [activeRegionSurface_eq_image] at hy
    obtain ⟨a, ha, hay⟩ := hy
    let u : P := ⟨a, ha⟩
    have hyt : dist y (f u) ≤ B * latticeRadius R (k + t) := by
      rw [← hay]
      exact htail t u
    refine ⟨f u, ⟨u, rfl⟩, ?_⟩
    have ht := dist_triangle x y (f u)
    dsimp [C]
    nlinarith
  have hdecay : Tendsto (fun t : ℕ => C * latticeRadius R (k + t)) atTop (𝓝 0) := by
    simp_rw [latticeRadius_add]
    simpa only [mul_zero] using!
      ((tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 64)
        (by norm_num : (1 / 64 : ℝ) < 1)).const_mul (latticeRadius R k)).const_mul C
  have hcl : x ∈ closure (Set.range f) := by
    rw [Metric.mem_closure_iff]
    intro δ hδ
    obtain ⟨t, ht⟩ := (hdecay.eventually (gt_mem_nhds hδ)).exists
    obtain ⟨y, hy, hxy⟩ := happrox t
    exact ⟨y, hy, hxy.trans_lt ht⟩
  exact hclosed.closure_eq ▸ hcl

end

end RieszRectifiability

end OAI
