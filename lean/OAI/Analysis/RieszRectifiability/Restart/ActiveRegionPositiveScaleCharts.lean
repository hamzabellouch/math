import Mathlib
import OAI.Analysis.RieszRectifiability.Restart.ActiveRegionTransitionMovement

namespace OAI

/-!
A lower stopping-scale bound lets finite-stage charts capture a nearby part of the limit surface.
The resulting chart retains the quantitative Lipschitz bound from the transition maps.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped NNReal

theorem exists_active_region_positive_scale_chart {n d : ℕ}
    (μ : Measure (Ambient d)) (R : ℝ) (hR : 0 < R) (k : ℕ)
    (z : (supportLatticeNets μ R hR k).points)
    (Good : SupportCellDescendant μ R hR k z → Prop)
    (S : SupportCellDescendant μ R hR k z → AffineSubspace ℝ (Ambient d))
    (hS : ∀ i, IsAffineNPlane n (S i)) (ε : ℝ) (hε : 0 < ε)
    (hεtiny : ε ≤ 1 / 268435456) (hsmall : activeProjectionError d ε ≤ 1 / 128)
    (hfit : ∀ i, activeRegionCell Good i →
      bilateralPlaneError μ i.center (1024 * i.radius) (S i) < ε)
    (f : S (supportCellRoot μ R hR k z) → Ambient d)
    (hmodel : IsActiveRegionLimitModel μ R hR k z Good S hS ε f)
    (q : SupportCellDescendant μ R hR k z) (hq : activeRegionCell Good q)
    (A : Set (Ambient d))
    (hnear : A ⊆ closedBall q.center ((17 / 8 : ℝ) * q.radius))
    (hscale : ∀ x ∈ A, q.radius / 8192 ≤ cellRegionStoppingScale μ R hR k z Good x) :
    ∃ g : closedBall ((S q).direction.orthogonalProjectionOnto q.center)
        ((5 / 2 : ℝ) * q.radius) → Ambient d,
      LipschitzWith ((activeProjectionGlobalLipschitzConstant d) ^ 3 * 2) g ∧
      Set.range f ∩ A ⊆ Set.range g := by
  have hqF : q ∈ activeLevelIndex μ R hR k z Good q.depth :=
    (mem_activeLevelIndex μ R hR k z Good q.depth q).mpr ⟨rfl, hq⟩
  have hcharts := activeRegionSurface_charts μ R hR k z Good S hS ε hε hεtiny hsmall hfit q.depth
  obtain ⟨g, hgLip, _, _, hgCapture⟩ := hcharts q hqF
  let T := activeRegionTransitionMap μ R hR k z Good S hS q.depth 3
  have hTLip := activeRegionTransitionMap_global_lipschitz μ R hR k z Good S hS q.depth
    ε (by linarith) hfit 3
  have hrq := q.radius_pos
  have hB : (17039360 * ε) / 63 ≤ 1 / 16 := by linarith
  have hrad : latticeRadius R (k + (q.depth + 3)) = q.radius / 262144 := by
    rw [← Nat.add_assoc, latticeRadius_add]
    change q.radius * (1 / 64 : ℝ) ^ 3 = _
    norm_num
    ring
  have hstable := active_region_limit_eq_finite_of_tail_small μ R hR k z Good S hS f
    (fun u => hmodel.2.2.1.tendsto_at u) ((17039360 * ε) / 63) (by positivity)
    hmodel.2.2.2.1 A (q.radius / 8192) hscale (q.depth + 3) (by
      rw [hrad]
      have hBm := mul_le_mul_of_nonneg_right hB hrq.le
      nlinarith)
  refine ⟨T ∘ g, hTLip.comp hgLip, ?_⟩
  intro x hx
  have hxN : x ∈ activeRegionSurface μ R hR k z Good S hS (q.depth + 3) :=
    (hstable ▸ hx).1
  rw [activeRegionSurface_add] at hxN
  obtain ⟨y, hy, hTy⟩ := hxN
  change T y = x at hTy
  have hmove := active_region_transition_surface_movement μ R hR k z Good S hS ε hε.le
    f hmodel q.depth 3 y hy
  change dist (T y) y ≤ (2 * ((17039360 * ε) / 63)) * q.radius at hmove
  rw [hTy] at hmove
  have hBm := mul_le_mul_of_nonneg_right hB hrq.le
  have hyq : y ∈ closedBall q.center ((9 / 4 : ℝ) * q.radius) := by
    have hxy := dist_triangle y x q.center
    rw [dist_comm y x] at hxy
    have hxq : dist x q.center ≤ (17 / 8 : ℝ) * q.radius := hnear hx.2
    change dist y q.center ≤ (9 / 4 : ℝ) * q.radius
    nlinarith
  have hyg : y ∈ Set.range g := (hgCapture ▸ (show y ∈
    activeRegionSurface μ R hR k z Good S hS q.depth ∩
      closedBall q.center ((9 / 4 : ℝ) * q.radius) from ⟨hy, hyq⟩)).1
  obtain ⟨u, hu⟩ := hyg
  refine ⟨u, ?_⟩
  change T (g u) = x
  rw [hu]
  exact hTy

end

end RieszRectifiability

end OAI
