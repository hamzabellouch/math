import Mathlib
import OAI.Analysis.RieszRectifiability.Restart.ActiveRegionSmallScaleArea

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set

theorem exists_active_surface_precision_below (d : ℕ) (δ : ℝ) (hδ : 0 < δ) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ δ ∧ ε ≤ 1 / 268435456 ∧ activeProjectionError d ε ≤ 1 / 128 := by
  obtain ⟨ε₀, hε₀, hε₀tiny, hη₀⟩ := exists_active_surface_precision d
  let ε := min ε₀ δ
  refine ⟨ε, lt_min hε₀ hδ, min_le_right _ _, (min_le_left _ _).trans hε₀tiny, ?_⟩
  apply le_trans _ hη₀
  unfold activeProjectionError
  exact mul_le_mul_of_nonneg_left (min_le_left ε₀ δ) (by positivity)

theorem exists_actual_active_region_limit_model_at_precision {n d : ℕ} (hnd : n ≤ d)
    (μ : Measure (Ambient d)) (R : ℝ) (hR : 0 < R) (k : ℕ)
    (z : (supportLatticeNets μ R hR k).points) (δ : ℝ) (hδ : 0 < δ) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ δ ∧ ε ≤ 1 / 268435456 ∧ activeProjectionError d ε ≤ 1 / 128 ∧
      let Good := fun q : SupportCellDescendant μ R hR k z =>
        bilateralBeta n μ q.center (1024 * q.radius) < ε
      ∃ (S : SupportCellDescendant μ R hR k z → AffineSubspace ℝ (Ambient d))
        (hS : ∀ i, IsAffineNPlane n (S i)),
        (∀ i, activeRegionCell Good i → bilateralPlaneError μ i.center (1024 * i.radius) (S i) < ε) ∧
        ∃ f : S (supportCellRoot μ R hR k z) → Ambient d,
          IsActiveRegionLimitModel μ R hR k z Good S hS ε f := by
  obtain ⟨ε, hε, hεδ, hεtiny, hsmall⟩ := exists_active_surface_precision_below d δ hδ
  let Good := fun q : SupportCellDescendant μ R hR k z =>
    bilateralBeta n μ q.center (1024 * q.radius) < ε
  obtain ⟨S, hS, hfit, _⟩ := exists_active_level_projection_maps μ R hR k z hnd ε hε
  exact ⟨ε, hε, hεδ, hεtiny, hsmall, S, hS, hfit,
    exists_active_region_limit_model μ R hR k z Good S hS ε hε hεtiny hsmall hfit⟩

end

end RieszRectifiability

end OAI
