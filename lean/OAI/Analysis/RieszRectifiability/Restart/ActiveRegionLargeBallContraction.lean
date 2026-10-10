import Mathlib
import OAI.Analysis.RieszRectifiability.Restart.ActiveRegionLimitEmbedding
import OAI.Analysis.RieszRectifiability.Foundations.BoundedDisplacementConvexContraction

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Topology

theorem exists_active_region_large_ball_contraction {n d : ℕ}
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
    (r : ℝ) (hr : 0 < r) (hrlarge : latticeRadius R k / 8192 ≤ r) :
    ∃ F : unitInterval × ↥(Set.range f ∩ closedBall p r) → Ambient d,
      Continuous F ∧ (∀ x, F (0, x) = x.val) ∧ (∀ x, F (1, x) = p) ∧
      (∀ s, F (s, ⟨p, ⟨hp, mem_closedBall_self hr.le⟩⟩) = p) ∧
      (∀ w, F w ∈ Set.range f ∩ closedBall p (2049 * r)) := by
  let B := (17039360 * ε) / 63
  have hB : B ≤ 1 / 16 := by dsimp [B]; linarith
  have hBm := mul_le_mul_of_nonneg_right hB (latticeRadius_pos R hR k).le
  have hf := (active_region_limit_isClosedEmbedding μ R hR k z Good S hS
    ε hε hεtiny hsmall hfit f hmodel).isEmbedding
  have hdisp : ∀ u : S (supportCellRoot μ R hR k z),
      dist (f u) (u : Ambient d) ≤ B * latticeRadius R k := by
    intro u
    have h := hmodel.2.2.2.1 0 u
    simp only [activeRegionParameterMap, id_eq, Nat.add_zero] at h
    rw [dist_comm]
    exact h
  have hpA : p ∈ Set.range f ∩ closedBall p r := ⟨hp, mem_closedBall_self hr.le⟩
  obtain ⟨F, hF, hzero, hone, hfixed, hball⟩ :=
    exists_bounded_displacement_convex_chart_contraction
      (S (supportCellRoot μ R hR k z) : Set (Ambient d))
      (S (supportCellRoot μ R hR k z)).convex f hf (B * latticeRadius R k) hdisp
      (Set.range f ∩ closedBall p r) (fun _ hx => hx.1) p hpA r (fun _ hx => hx.2)
  refine ⟨F, hF, hzero, hone, hfixed, ?_⟩
  intro w
  refine ⟨(hball w).1, ?_⟩
  have hb : dist (F w) p ≤ r + 4 * (B * latticeRadius R k) := (hball w).2
  change dist (F w) p ≤ 2049 * r
  nlinarith

end

end RieszRectifiability

end OAI
