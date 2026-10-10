import Mathlib
import OAI.Analysis.RieszRectifiability.Restart.ActiveScaleBallSelection
import OAI.Analysis.RieszRectifiability.Restart.ActiveRegionPositiveScaleBiCharts
import OAI.Analysis.RieszRectifiability.Surfaces.QuantitativeConvexChartContraction

namespace OAI

/-!
A positive stopping scale supplies a bilipschitz chart on a convex plane ball. Contracting inside
that chart gives a controlled small-ball contraction; finite-stage stabilization keeps its image
on the limiting active-region surface.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Topology

theorem exists_active_region_positive_scale_small_ball_contraction {n d : ℕ}
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
    (hDpos : 0 < cellRegionStoppingScale μ R hR k z Good p)
    (hDsmall : cellRegionStoppingScale μ R hR k z Good p < latticeRadius R (k + 1))
    (r : ℝ) (hr : 0 < r) (hrsmall : r ≤ cellRegionStoppingScale μ R hR k z Good p / 2048) :
    ∃ F : unitInterval × ↥(Set.range f ∩ closedBall p r) → Ambient d,
      Continuous F ∧ (∀ x, F (0, x) = x.val) ∧ (∀ x, F (1, x) = p) ∧
      (∀ s, F (s, ⟨p, ⟨hp, mem_closedBall_self hr.le⟩⟩) = p) ∧
      (∀ w, F w ∈ Set.range f ∩ closedBall p (1024 * r)) := by
  let δ := cellRegionStoppingScale μ R hR k z Good p
  let B := (17039360 * ε) / 63
  obtain ⟨q, hq, hqhi, hqlo, hnear⟩ :=
    exists_active_parent_at_stopping_scale μ R hR k z Good p hDpos hDsmall
  obtain ⟨hball, hscale⟩ := active_stopping_ball_chart_geometry μ R hR k z Good p q hqhi hqlo hnear
  have hsub : closedBall p r ⊆ closedBall p (δ / 16) := by
    intro x hx
    have hx' : dist x p ≤ r := hx
    change dist x p ≤ δ / 16
    change r ≤ δ / 2048 at hrsmall
    change 0 < δ at hDpos
    linarith
  obtain ⟨H, hHLip, hHsep, hHfinite, hcapture⟩ :=
    exists_active_region_positive_scale_bilipschitz_chart μ R hR k z Good S hS
      ε hε hεtiny hsmall hfit f hmodel q hq (closedBall p r)
      (hsub.trans hball) (fun x hx => hscale x (hsub hx))
  have hpA : p ∈ Set.range f ∩ closedBall p r := ⟨hp, mem_closedBall_self hr.le⟩
  obtain ⟨F, hF, hzero, hone, hfixed, hFrange⟩ :=
    exists_bounded_contraction_in_bilipschitz_convex_chart
      (closedBall ((S q).direction.orthogonalProjectionOnto q.center) ((5 / 2 : ℝ) * q.radius))
      (convex_closedBall _ _) H 16 64 hHLip hHsep
      (Set.range f ∩ closedBall p r) hcapture p hpA r (fun _ hx => hx.2)
  have hB : B ≤ 1 / 16 := by dsimp [B]; linarith
  have hrad : latticeRadius R (k + (q.depth + 3)) = q.radius / 262144 := by
    rw [← Nat.add_assoc, latticeRadius_add]
    change q.radius * (1 / 64 : ℝ) ^ 3 = _
    norm_num
    ring
  have hK : ∀ x ∈ closedBall p (δ / 2), δ / 2 ≤ cellRegionStoppingScale μ R hR k z Good x := by
    intro x hx
    have h := cellRegionStoppingScale_le_add_dist μ R hR k z Good p x
    rw [dist_comm p x] at h
    change δ ≤ cellRegionStoppingScale μ R hR k z Good x + dist x p at h
    have hx' : dist x p ≤ δ / 2 := hx
    linarith
  have hstable := active_region_limit_eq_finite_of_tail_small μ R hR k z Good S hS f
    (fun u => hmodel.2.2.1.tendsto_at u) B (by dsimp [B]; positivity)
    hmodel.2.2.2.1 (closedBall p (δ / 2)) (δ / 2) hK (q.depth + 3) (by
      rw [hrad]
      have hBm := mul_le_mul_of_nonneg_right hB q.radius_pos.le
      change q.radius ≤ 4096 * δ at hqhi
      change 0 < δ at hDpos
      nlinarith)
  refine ⟨F, hF, hzero, hone, hfixed, ?_⟩
  intro w
  have hw : F w ∈ Set.range H ∩ closedBall p (1024 * r) := by
    simpa only [NNReal.coe_ofNat, show (16 : ℝ) * 64 = 1024 by norm_num] using! hFrange w
  have hwK : F w ∈ closedBall p (δ / 2) := by
    have hb : dist (F w) p ≤ 1024 * r := hw.2
    change dist (F w) p ≤ δ / 2
    change r ≤ δ / 2048 at hrsmall
    linarith
  have hin : F w ∈ Set.range f :=
    (hstable.symm ▸ (show F w ∈ activeRegionSurface μ R hR k z Good S hS (q.depth + 3) ∩
      closedBall p (δ / 2) from ⟨hHfinite hw.1, hwK⟩)).1
  exact ⟨hin, hw.2⟩

end

end RieszRectifiability

end OAI
