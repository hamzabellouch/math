import Mathlib
import OAI.Analysis.RieszRectifiability.Restart.ActiveRegionTransitions
import OAI.Analysis.RieszRectifiability.Restart.ActiveSurfaceNonCollapse

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set

theorem activeRegionTransitionMap_surface_dist_bounds {n d : ℕ}
    (μ : Measure (Ambient d)) (R : ℝ) (hR : 0 < R) (k : ℕ)
    (z : (supportLatticeNets μ R hR k).points)
    (Good : SupportCellDescendant μ R hR k z → Prop)
    (S : SupportCellDescendant μ R hR k z → AffineSubspace ℝ (Ambient d))
    (hS : ∀ i, IsAffineNPlane n (S i)) (ε : ℝ) (hε : 0 < ε)
    (hεtiny : ε ≤ 1 / 268435456) (hsmall : activeProjectionError d ε ≤ 1 / 128)
    (hfit : ∀ i, activeRegionCell Good i →
      bilateralPlaneError μ i.center (1024 * i.radius) (S i) < ε)
    (s j : ℕ) (x y : Ambient d)
    (hx : x ∈ activeRegionSurface μ R hR k z Good S hS s)
    (hy : y ∈ activeRegionSurface μ R hR k z Good S hS s) :
    (1 / 4 : ℝ) ^ j * dist x y ≤
        dist (activeRegionTransitionMap μ R hR k z Good S hS s j x)
          (activeRegionTransitionMap μ R hR k z Good S hS s j y) ∧
      dist (activeRegionTransitionMap μ R hR k z Good S hS s j x)
        (activeRegionTransitionMap μ R hR k z Good S hS s j y) ≤ 2 ^ j * dist x y := by
  induction j with
  | zero =>
    simp only [pow_zero, one_mul, activeRegionTransitionMap, id_eq]
    exact ⟨le_rfl, le_rfl⟩
  | succ j ih =>
    have hcharts := activeRegionSurface_charts μ R hR k z Good S hS
      ε hε hεtiny hsmall hfit (s + j)
    have hTx : activeRegionTransitionMap μ R hR k z Good S hS s j x ∈
        activeRegionSurface μ R hR k z Good S hS (s + j) := by
      rw [activeRegionSurface_add]
      exact ⟨x, hx, rfl⟩
    have hTy : activeRegionTransitionMap μ R hR k z Good S hS s j y ∈
        activeRegionSurface μ R hR k z Good S hS (s + j) := by
      rw [activeRegionSurface_add]
      exact ⟨y, hy, rfl⟩
    have hstep := activeLevelProjectionMap_surface_dist_bounds μ R hR k z Good (s + j)
      S hS ε hε (by linarith) hfit (activeRegionSurface μ R hR k z Good S hS (s + j))
      hcharts hsmall (activeRegionTransitionMap μ R hR k z Good S hS s j x)
      (activeRegionTransitionMap μ R hR k z Good S hS s j y) hTx hTy
    constructor
    · calc
        (1 / 4 : ℝ) ^ (j + 1) * dist x y = (1 / 4 : ℝ) * ((1 / 4 : ℝ) ^ j * dist x y) := by
          rw [pow_succ]
          ring
        _ ≤ (1 / 4 : ℝ) * dist (activeRegionTransitionMap μ R hR k z Good S hS s j x)
            (activeRegionTransitionMap μ R hR k z Good S hS s j y) :=
          mul_le_mul_of_nonneg_left ih.1 (by norm_num)
        _ ≤ _ := hstep.1
    · calc
        _ ≤ 2 * dist (activeRegionTransitionMap μ R hR k z Good S hS s j x)
            (activeRegionTransitionMap μ R hR k z Good S hS s j y) := hstep.2
        _ ≤ 2 * (2 ^ j * dist x y) := mul_le_mul_of_nonneg_left ih.2 (by norm_num)
        _ = 2 ^ (j + 1) * dist x y := by rw [pow_succ]; ring

end

end RieszRectifiability

end OAI
