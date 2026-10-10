import Mathlib
import OAI.Analysis.RieszRectifiability.Restart.ActiveRegionSurfaces
import OAI.Analysis.RieszRectifiability.Restart.ActiveSurfaceNonCollapse

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set

theorem activeRegionParameterMap_dist_bounds {n d : ℕ}
    (μ : Measure (Ambient d)) (R : ℝ) (hR : 0 < R) (k : ℕ)
    (z : (supportLatticeNets μ R hR k).points)
    (Good : SupportCellDescendant μ R hR k z → Prop)
    (S : SupportCellDescendant μ R hR k z → AffineSubspace ℝ (Ambient d))
    (hS : ∀ i, IsAffineNPlane n (S i)) (ε : ℝ) (hε : 0 < ε)
    (hεtiny : ε ≤ 1 / 268435456) (hsmall : activeProjectionError d ε ≤ 1 / 128)
    (hfit : ∀ i, activeRegionCell Good i →
      bilateralPlaneError μ i.center (1024 * i.radius) (S i) < ε)
    (t : ℕ) (u v : (S (supportCellRoot μ R hR k z) : Set (Ambient d))) :
    (1 / 4 : ℝ) ^ t * dist u v ≤
        dist (activeRegionParameterMap μ R hR k z Good S hS t u)
          (activeRegionParameterMap μ R hR k z Good S hS t v) ∧
      dist (activeRegionParameterMap μ R hR k z Good S hS t u)
        (activeRegionParameterMap μ R hR k z Good S hS t v) ≤ 2 ^ t * dist u v := by
  induction t with
  | zero =>
    simp only [pow_zero, one_mul, activeRegionParameterMap, id_eq, Subtype.dist_eq]
    exact ⟨le_rfl, le_rfl⟩
  | succ t ih =>
    have hcharts := activeRegionSurface_charts μ R hR k z Good S hS ε hε hεtiny hsmall hfit t
    have hu : activeRegionParameterMap μ R hR k z Good S hS t u ∈
        activeRegionSurface μ R hR k z Good S hS t := by
      rw [activeRegionSurface_eq_image]
      exact ⟨u.val, u.property, rfl⟩
    have hv : activeRegionParameterMap μ R hR k z Good S hS t v ∈
        activeRegionSurface μ R hR k z Good S hS t := by
      rw [activeRegionSurface_eq_image]
      exact ⟨v.val, v.property, rfl⟩
    have hstep := activeLevelProjectionMap_surface_dist_bounds μ R hR k z Good t
      S hS ε hε (by linarith) hfit (activeRegionSurface μ R hR k z Good S hS t)
      hcharts hsmall (activeRegionParameterMap μ R hR k z Good S hS t u)
      (activeRegionParameterMap μ R hR k z Good S hS t v) hu hv
    constructor
    · calc
        (1 / 4 : ℝ) ^ (t + 1) * dist u v = (1 / 4 : ℝ) * ((1 / 4 : ℝ) ^ t * dist u v) := by
          rw [pow_succ]
          ring
        _ ≤ (1 / 4 : ℝ) * dist (activeRegionParameterMap μ R hR k z Good S hS t u)
            (activeRegionParameterMap μ R hR k z Good S hS t v) :=
          mul_le_mul_of_nonneg_left ih.1 (by norm_num)
        _ ≤ _ := hstep.1
    · calc
        _ ≤ 2 * dist (activeRegionParameterMap μ R hR k z Good S hS t u)
            (activeRegionParameterMap μ R hR k z Good S hS t v) := hstep.2
        _ ≤ 2 * (2 ^ t * dist u v) := mul_le_mul_of_nonneg_left ih.2 (by norm_num)
        _ = 2 ^ (t + 1) * dist u v := by rw [pow_succ]; ring

end

end RieszRectifiability

end OAI
