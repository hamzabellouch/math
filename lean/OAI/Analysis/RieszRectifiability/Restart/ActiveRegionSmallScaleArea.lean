import Mathlib
import OAI.Analysis.RieszRectifiability.Restart.ActiveRegionStoppingBallArea
import OAI.Analysis.RieszRectifiability.Kernel.NearSupportMassCharge

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped NNReal ENNReal

def activeRegionSmallScaleAreaConstant (n d : ℕ) (C : ℝ) : ℝ≥0∞ :=
  (activeRegionLocalAreaConstant n d * (4096 : ℝ≥0∞) ^ n) *
    ENNReal.ofReal (C * 256 ^ n)

theorem activeRegionSmallScaleAreaConstant_lt_top (n d : ℕ) (C : ℝ) :
    activeRegionSmallScaleAreaConstant n d C < ⊤ := by
  exact ENNReal.mul_lt_top
    (ENNReal.mul_lt_top (activeRegionLocalAreaConstant_lt_top n d) (by finiteness))
    ENNReal.ofReal_lt_top

theorem active_region_small_positive_scale_area_le {n d : ℕ}
    (μ : Measure (Ambient d)) (C : ℝ) (hC : 0 < C)
    (hlower : ∀ a ∈ μ.support, ∀ r : ℝ, AdmissibleRadius μ r →
      ENNReal.ofReal (r ^ n / C) ≤ μ (ball a r))
    (R : ℝ) (hR : 0 < R) (k : ℕ)
    (hcore : AdmissibleRadius μ (latticeRadius R k / 8))
    (z : (supportLatticeNets μ R hR k).points)
    (Good : SupportCellDescendant μ R hR k z → Prop)
    (S : SupportCellDescendant μ R hR k z → AffineSubspace ℝ (Ambient d))
    (hS : ∀ i, IsAffineNPlane n (S i)) (ε : ℝ) (hε : 0 < ε)
    (hεfine : ε ≤ 1 / 281474976710656) (hsmall : activeProjectionError d ε ≤ 1 / 128)
    (hfit : ∀ i, activeRegionCell Good i →
      bilateralPlaneError μ i.center (1024 * i.radius) (S i) < ε)
    (f : S (supportCellRoot μ R hR k z) → Ambient d)
    (hmodel : IsActiveRegionLimitModel μ R hR k z Good S hS ε f)
    (A : Set (Ambient d))
    (hA : A ⊆ Set.range f ∩ closedBall (z : Ambient d) (2 * latticeRadius R k))
    (hD : ∀ x ∈ A, 0 < cellRegionStoppingScale μ R hR k z Good x ∧
      cellRegionStoppingScale μ R hR k z Good x < latticeRadius R (k + 1)) :
    (μH[(n : ℝ)] : Measure (Ambient d)) A ≤
      activeRegionSmallScaleAreaConstant n d C *
        μ (closedBall (z : Ambient d) (3 * latticeRadius R k)) := by
  let D := cellRegionStoppingScale μ R hR k z Good
  have hεtiny : ε ≤ 1 / 268435456 := by linarith
  have hr0 := latticeRadius_pos R hR k
  have hμ : μ.support.Nonempty := ⟨z, (supportLatticeNets μ R hR k).subset z.property⟩
  apply measure_le_of_local_fivefold_charges (μH[(n : ℝ)] : Measure (Ambient d)) μ A
    (closedBall (z : Ambient d) (3 * latticeRadius R k)) (fun x => D x / 128)
    (latticeRadius R k / 128)
  · intro x hx
    exact div_pos (hD x hx).1 (by norm_num)
  · intro x _
    exact div_le_div_of_nonneg_right (cellRegionStoppingScale_le_top μ R hR k z Good x)
      (by norm_num)
  · intro x hx y hy
    have hxy : dist y x ≤ D x / 128 := hy
    have hxz : dist x (z : Ambient d) ≤ 2 * latticeRadius R k := (hA hx).2
    have hcap := cellRegionStoppingScale_le_top μ R hR k z Good x
    have ht := dist_triangle y x (z : Ambient d)
    change dist y (z : Ambient d) ≤ 3 * latticeRadius R k
    change D x ≤ latticeRadius R k at hcap
    linarith
  · intro x hx
    have hDx : 0 < D x := (hD x hx).1
    have hcap : D x ≤ latticeRadius R k := cellRegionStoppingScale_le_top μ R hR k z Good x
    have hadm : AdmissibleRadius μ (D x / 256) := by
      refine ⟨by positivity, ?_⟩
      exact (ENNReal.ofReal_le_ofReal (show D x / 256 ≤ latticeRadius R k / 8 by linarith)).trans hcore.2
    have hclose := active_region_limit_support_distance_at_scale μ R hR k z Good S hS ε hε
      hεtiny hsmall hfit f hmodel x (hA hx).1 (hD x hx).1 (hD x hx).2
    have hnear : infDist x μ.support ≤ D x / 512 := by
      change infDist x μ.support ≤ (2187264000 * ε) * D x at hclose
      have hm := mul_le_mul_of_nonneg_right hεfine hDx.le
      nlinarith
    have hmass := near_support_radius_power_le_mass μ hμ C hC hlower x (D x) hDx hadm hnear
    have harea := active_region_stopping_ball_area_le μ R hR k z Good S hS ε hε hεtiny hsmall
      hfit f hmodel x (hD x hx).1 (hD x hx).2
    have hsub : A ∩ closedBall x (5 * (D x / 128)) ⊆
        Set.range f ∩ closedBall x (D x / 16) := by
      intro y hy
      exact ⟨(hA hy.1).1, closedBall_subset_closedBall (by linarith) hy.2⟩
    calc
      _ ≤ (μH[(n : ℝ)] : Measure (Ambient d))
          (Set.range f ∩ closedBall x (D x / 16)) := measure_mono hsub
      _ ≤ (activeRegionLocalAreaConstant n d * (4096 : ℝ≥0∞) ^ n) * (ENNReal.ofReal (D x)) ^ n := harea
      _ ≤ (activeRegionLocalAreaConstant n d * (4096 : ℝ≥0∞) ^ n) *
          (ENNReal.ofReal (C * 256 ^ n) * μ (closedBall x (D x / 128))) := mul_le_mul_right hmass _
      _ = _ := by unfold activeRegionSmallScaleAreaConstant; simp only [mul_assoc]

end

end RieszRectifiability

end OAI
