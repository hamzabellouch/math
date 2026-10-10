import Mathlib
import OAI.Analysis.RieszRectifiability.Restart.ActiveRegionTransitionDistortion

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set

theorem activeRegionTransitionMap_surface_residual_le {n d : ℕ}
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
    ‖(activeRegionTransitionMap μ R hR k z Good S hS s j x -
      activeRegionTransitionMap μ R hR k z Good S hS s j y) - (x - y)‖ ≤
        (72 * activeProjectionError d ε) * ((2 : ℝ) ^ j - 1) * dist x y := by
  let K := 72 * activeProjectionError d ε
  have hK : 0 ≤ K := by dsimp [K, activeProjectionError]; positivity
  change _ ≤ K * ((2 : ℝ) ^ j - 1) * dist x y
  induction j with
  | zero => simp only [activeRegionTransitionMap, id_eq, sub_self, norm_zero, pow_zero, mul_zero, zero_mul, le_refl]
  | succ j ih =>
    let T := activeRegionTransitionMap μ R hR k z Good S hS s j
    let σ := activeLevelProjectionMap μ R hR k z Good (s + j + 1) S hS
    have hTx : T x ∈ activeRegionSurface μ R hR k z Good S hS (s + j) := by
      rw [activeRegionSurface_add]
      exact ⟨x, hx, rfl⟩
    have hTy : T y ∈ activeRegionSurface μ R hR k z Good S hS (s + j) := by
      rw [activeRegionSurface_add]
      exact ⟨y, hy, rfl⟩
    have hcharts := activeRegionSurface_charts μ R hR k z Good S hS
      ε hε hεtiny hsmall hfit (s + j)
    have hstep := activeLevelProjectionMap_surface_residual_le μ R hR k z Good (s + j)
      S hS ε hε (by linarith) hfit (activeRegionSurface μ R hR k z Good S hS (s + j))
      hcharts (T x) (T y) hTx hTy
    have hdist := (activeRegionTransitionMap_surface_dist_bounds μ R hR k z Good S hS
      ε hε hεtiny hsmall hfit s j x y hx hy).2
    change ‖(σ (T x) - σ (T y)) - (T x - T y)‖ ≤ K * dist (T x) (T y) at hstep
    change dist (T x) (T y) ≤ (2 : ℝ) ^ j * dist x y at hdist
    change ‖(T x - T y) - (x - y)‖ ≤ K * ((2 : ℝ) ^ j - 1) * dist x y at ih
    change ‖(σ (T x) - σ (T y)) - (x - y)‖ ≤ _
    have hid : (σ (T x) - σ (T y)) - (x - y) =
        ((σ (T x) - σ (T y)) - (T x - T y)) + ((T x - T y) - (x - y)) := by abel
    calc
      _ ≤ ‖(σ (T x) - σ (T y)) - (T x - T y)‖ + ‖(T x - T y) - (x - y)‖ := by
        rw [hid]
        exact norm_add_le _ _
      _ ≤ K * dist (T x) (T y) + K * ((2 : ℝ) ^ j - 1) * dist x y := add_le_add hstep ih
      _ ≤ K * ((2 : ℝ) ^ j * dist x y) + K * ((2 : ℝ) ^ j - 1) * dist x y :=
        add_le_add (mul_le_mul_of_nonneg_left hdist hK) le_rfl
      _ = K * ((2 : ℝ) ^ (j + 1) - 1) * dist x y := by rw [pow_succ]; ring

end

end RieszRectifiability

end OAI
