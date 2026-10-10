import Mathlib
import OAI.Analysis.RieszRectifiability.Restart.ActiveRegionLimitModel
import OAI.Analysis.RieszRectifiability.Surfaces.QuantitativeConvexChartContraction
import OAI.Analysis.RieszRectifiability.Restart.ActiveRegionChartLift

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Topology

theorem exists_active_region_high_scale_small_ball_contraction {n d : ℕ}
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
    (p : Ambient d) (hp : p ∈ Set.range f)
    (hD : latticeRadius R (k + 1) ≤ cellRegionStoppingScale μ R hR k z Good p)
    (r : ℝ) (hr : 0 < r) (hrsmall : r ≤ latticeRadius R k / 8192) :
    ∃ F : unitInterval × ↥(Set.range f ∩ closedBall p r) → Ambient d,
      Continuous F ∧ (∀ x, F (0, x) = x.val) ∧ (∀ x, F (1, x) = p) ∧
      (∀ s, F (s, ⟨p, ⟨hp, mem_closedBall_self hr.le⟩⟩) = p) ∧
      (∀ w, F w ∈ Set.range f ∩ closedBall p (64 * r)) := by
  let B := (17039360 * ε) / 63
  let H := fun u : S (supportCellRoot μ R hR k z) =>
    activeRegionParameterMap μ R hR k z Good S hS 2 u
  have hHLip : LipschitzWith 4 H := by
    apply LipschitzWith.of_dist_le_mul
    intro u v
    have h := (activeRegionParameterMap_dist_bounds μ R hR k z Good S hS
      ε hε hεtiny hsmall hfit 2 u v).2
    norm_num at h ⊢
    exact h
  have hHsep : AntilipschitzWith 16 H := by
    have h := activeRegionParameterMap_antilipschitz μ R hR k z Good S hS
      ε hε hεtiny hsmall hfit 2
    norm_num at h
    exact h
  have hHrange : Set.range H = activeRegionSurface μ R hR k z Good S hS 2 := by
    rw [activeRegionSurface_eq_image]
    ext x
    constructor
    · rintro ⟨u, rfl⟩
      exact ⟨u.val, u.property, rfl⟩
    · rintro ⟨u, hu, hux⟩
      exact ⟨⟨u, hu⟩, hux⟩
  have hr0 := latticeRadius_pos R hR k
  have hB : B ≤ 1 / 16 := by dsimp [B]; linarith
  have hBm := mul_le_mul_of_nonneg_right hB hr0.le
  have hrad : latticeRadius R (k + 2) = latticeRadius R k / 4096 := by
    rw [latticeRadius_add]
    norm_num
    ring
  rw [latticeRadius_succ] at hD
  have hK : ∀ x ∈ closedBall p (latticeRadius R k / 128),
      latticeRadius R k / 128 ≤ cellRegionStoppingScale μ R hR k z Good x := by
    intro x hx
    have h := cellRegionStoppingScale_le_add_dist μ R hR k z Good p x
    rw [dist_comm p x] at h
    have hb : dist x p ≤ latticeRadius R k / 128 := hx
    linarith
  have hstable := active_region_limit_eq_finite_of_tail_small μ R hR k z Good S hS f
    (fun u => hmodel.2.2.1.tendsto_at u) B (by dsimp [B]; positivity)
    hmodel.2.2.2.1 (closedBall p (latticeRadius R k / 128))
    (latticeRadius R k / 128) hK 2 (by rw [hrad]; nlinarith)
  have hcapture : Set.range f ∩ closedBall p r ⊆ Set.range H := by
    intro x hx
    have hxK : x ∈ closedBall p (latticeRadius R k / 128) := by
      have hb : dist x p ≤ r := hx.2
      change dist x p ≤ latticeRadius R k / 128
      linarith
    rw [hHrange]
    exact (hstable ▸ (show x ∈ Set.range f ∩ closedBall p (latticeRadius R k / 128)
      from ⟨hx.1, hxK⟩)).1
  have hpA : p ∈ Set.range f ∩ closedBall p r := ⟨hp, mem_closedBall_self hr.le⟩
  obtain ⟨F, hF, hzero, hone, hfixed, hball⟩ :=
    exists_bounded_contraction_in_bilipschitz_convex_chart
      (S (supportCellRoot μ R hR k z) : Set (Ambient d))
      (S (supportCellRoot μ R hR k z)).convex H 4 16 hHLip hHsep
      (Set.range f ∩ closedBall p r) hcapture p hpA r (fun _ hx => hx.2)
  refine ⟨F, hF, hzero, hone, hfixed, ?_⟩
  intro w
  have hw : F w ∈ Set.range H ∩ closedBall p (64 * r) := by
    simpa only [NNReal.coe_ofNat, show (4 : ℝ) * 16 = 64 by norm_num] using! hball w
  have hwK : F w ∈ closedBall p (latticeRadius R k / 128) := by
    have hb : dist (F w) p ≤ 64 * r := hw.2
    change dist (F w) p ≤ latticeRadius R k / 128
    linarith
  have hin : F w ∈ Set.range f :=
    (hstable.symm ▸ (show F w ∈ activeRegionSurface μ R hR k z Good S hS 2 ∩
      closedBall p (latticeRadius R k / 128) from ⟨hHrange ▸ hw.1, hwK⟩)).1
  exact ⟨hin, hw.2⟩

end

end RieszRectifiability

end OAI
