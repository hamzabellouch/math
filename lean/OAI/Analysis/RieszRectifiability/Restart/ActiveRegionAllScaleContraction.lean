import Mathlib
import OAI.Analysis.RieszRectifiability.Restart.ActiveRegionMediumScaleContraction
import OAI.Analysis.RieszRectifiability.Restart.ActiveRegionHighScaleContraction
import OAI.Analysis.RieszRectifiability.Restart.ActiveRegionLargeBallContraction

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Topology

def HasBoundedBallContractions {d : ℕ} (A : Set (Ambient d)) (C : ℝ) : Prop :=
  ∀ (p : Ambient d) (hp : p ∈ A) (r : ℝ) (hr : 0 < r),
    ∃ F : unitInterval × ↥(A ∩ closedBall p r) → Ambient d,
      Continuous F ∧ (∀ x, F (0, x) = x.val) ∧ (∀ x, F (1, x) = p) ∧
      (∀ s, F (s, ⟨p, ⟨hp, mem_closedBall_self hr.le⟩⟩) = p) ∧
      (∀ w, F w ∈ A ∩ closedBall p (C * r))

theorem active_region_limit_has_bounded_ball_contractions {n d : ℕ}
    (μ : Measure (Ambient d)) (R : ℝ) (hR : 0 < R) (k : ℕ)
    (z : (supportLatticeNets μ R hR k).points)
    (Good : SupportCellDescendant μ R hR k z → Prop)
    (S : SupportCellDescendant μ R hR k z → AffineSubspace ℝ (Ambient d))
    (hS : ∀ i, IsAffineNPlane n (S i)) (ε : ℝ) (hε : 0 < ε)
    (hεtiny : ε ≤ 1 / 268435456) (hsmall : activeProjectionError d ε ≤ 1 / 128)
    (hfit : ∀ i, activeRegionCell Good i →
      bilateralPlaneError μ i.center (1024 * i.radius) (S i) < ε)
    (f : S (supportCellRoot μ R hR k z) → Ambient d)
    (hmodel : IsActiveRegionLimitModel μ R hR k z Good S hS ε f) :
    HasBoundedBallContractions (Set.range f) 50331648 := by
  intro p hp r hr
  by_cases hlarge : latticeRadius R k / 8192 ≤ r
  · obtain ⟨F, hF, hzero, hone, hfixed, hball⟩ :=
      exists_active_region_large_ball_contraction μ R hR k z Good S hS
        ε hε hεtiny hsmall hfit f hmodel p hp r hr hlarge
    refine ⟨F, hF, hzero, hone, hfixed, ?_⟩
    intro w
    refine ⟨(hball w).1, ?_⟩
    have hb : dist (F w) p ≤ 2049 * r := (hball w).2
    change dist (F w) p ≤ 50331648 * r
    linarith
  have hr0 := latticeRadius_pos R hR k
  have hrsmall : r ≤ latticeRadius R k / 8192 := le_of_not_ge hlarge
  by_cases hhigh : latticeRadius R (k + 1) ≤ cellRegionStoppingScale μ R hR k z Good p
  · obtain ⟨F, hF, hzero, hone, hfixed, hball⟩ :=
      exists_active_region_high_scale_small_ball_contraction μ R hR k z Good S hS
        ε hε hεtiny hsmall hfit f hmodel p hp hhigh r hr hrsmall
    refine ⟨F, hF, hzero, hone, hfixed, ?_⟩
    intro w
    refine ⟨(hball w).1, ?_⟩
    have hb : dist (F w) p ≤ 64 * r := (hball w).2
    change dist (F w) p ≤ 50331648 * r
    linarith
  exact exists_active_region_below_first_scale_ball_contraction μ R hR k z Good S hS
    ε hε hεtiny hsmall hfit f hmodel p hp (lt_of_not_ge hhigh) r hr (by linarith)

end

end RieszRectifiability

end OAI
