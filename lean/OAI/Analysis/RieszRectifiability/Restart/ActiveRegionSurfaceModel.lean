import Mathlib
import OAI.Analysis.RieszRectifiability.Restart.ActiveRegionSurfaceApproximation

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set

theorem exists_active_surface_precision (d : ℕ) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 / 268435456 ∧ activeProjectionError d ε ≤ 1 / 128 := by
  let C : ℝ := 2048 + 1048576 * (9 : ℝ) ^ d
  have hC : 0 < C := by dsimp [C]; positivity
  let ε := min (1 / 268435456 : ℝ) (1 / (128 * C))
  have hε : 0 < ε := lt_min (by norm_num) (by positivity)
  refine ⟨ε, hε, min_le_left _ _, ?_⟩
  have hb := mul_le_mul_of_nonneg_left (min_le_right (1 / 268435456 : ℝ) (1 / (128 * C))) hC.le
  have heq : C * (1 / (128 * C)) = 1 / 128 := by field_simp
  change C * ε ≤ 1 / 128
  exact hb.trans_eq heq

theorem exists_actual_active_region_surfaces {n d : ℕ} (hnd : n ≤ d)
    (μ : Measure (Ambient d)) (R : ℝ) (hR : 0 < R) (k : ℕ)
    (z : (supportLatticeNets μ R hR k).points)
    (ε : ℝ) (hε : 0 < ε) (hεtiny : ε ≤ 1 / 268435456)
    (hsmall : activeProjectionError d ε ≤ 1 / 128) :
    let Good := fun q : SupportCellDescendant μ R hR k z =>
      bilateralBeta n μ q.center (1024 * q.radius) < ε
    ∃ (S : SupportCellDescendant μ R hR k z → AffineSubspace ℝ (Ambient d))
      (hS : ∀ i, IsAffineNPlane n (S i)),
      (∀ i, activeRegionCell Good i → bilateralPlaneError μ i.center (1024 * i.radius) (S i) < ε) ∧
      ∀ t : ℕ,
        Continuous (activeRegionParameterMap μ R hR k z Good S hS t) ∧
        HasActiveSurfaceCharts μ R hR k z Good t S ε
          (activeRegionSurface μ R hR k z Good S hS t) ∧
        (∀ x ∈ cellRegionLimit μ R hR k z Good,
          ∃ y ∈ activeRegionSurface μ R hR k z Good S hS t,
            dist x y ≤ (263168 * ε) * latticeRadius R (k + t)) ∧
        (∀ x ∈ activeRegionSurface μ R hR k z Good S hS t,
          dist (activeLevelProjectionMap μ R hR k z Good (t + 1) S hS x) x ≤
            (17039360 * ε) * latticeRadius R (k + (t + 1))) := by
  let Good := fun q : SupportCellDescendant μ R hR k z =>
    bilateralBeta n μ q.center (1024 * q.radius) < ε
  obtain ⟨S, hS, hfit, _⟩ := exists_active_level_projection_maps μ R hR k z hnd ε hε
  refine ⟨S, hS, hfit, ?_⟩
  intro t
  exact ⟨activeRegionParameterMap_continuous μ R hR k z Good S hS t,
    activeRegionSurface_charts μ R hR k z Good S hS ε hε hεtiny hsmall hfit t,
    activeRegionSurface_approximates_region_limit μ R hR k z Good S hS ε hε hεtiny hsmall hfit t,
    activeRegionSurface_successor_displacement μ R hR k z Good S hS ε hε hεtiny hsmall hfit t⟩

end

end RieszRectifiability

end OAI
