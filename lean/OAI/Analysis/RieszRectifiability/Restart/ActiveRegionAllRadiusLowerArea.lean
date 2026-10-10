import Mathlib
import OAI.Analysis.RieszRectifiability.Restart.ActiveRegionSmallRadiusLowerArea
import OAI.Analysis.RieszRectifiability.Restart.ActiveRegionLargeRadiusLowerArea

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal

def activeRegionAllRadiusLowerAreaConstant (n : ℕ) (C G : ℝ) : ℝ≥0∞ :=
  min (activeRegionSmallRadiusLowerAreaConstant n C G * (ENNReal.ofReal (1 / 8 : ℝ)) ^ n)
    (activeRegionLargeRadiusLowerAreaConstant n)

theorem activeRegionAllRadiusLowerAreaConstant_pos (n : ℕ) (C G : ℝ) :
    0 < activeRegionAllRadiusLowerAreaConstant n C G := by
  apply lt_min
  · exact ENNReal.mul_pos (activeRegionSmallRadiusLowerAreaConstant_pos n C G).ne' (by positivity)
  · exact activeRegionLargeRadiusLowerAreaConstant_pos n

theorem activeRegionAllRadiusLowerAreaConstant_lt_top (n : ℕ) (C G : ℝ) :
    activeRegionAllRadiusLowerAreaConstant n C G < ⊤ :=
  lt_of_le_of_lt (min_le_right _ _) (activeRegionLargeRadiusLowerAreaConstant_lt_top n)

theorem active_region_limit_all_radius_ball_area_ge {n d : ℕ} (hn : 0 < n)
    (μ : Measure (Ambient d)) (C G : ℝ) (hC : 0 < C) (hG : 0 < G)
    (hg : GlobalUpperGrowth n G μ)
    (hlower : ∀ x ∈ μ.support, ∀ r : ℝ, AdmissibleRadius μ r →
      ENNReal.ofReal (r ^ n / C) ≤ μ (ball x r))
    (R : ℝ) (hR : 0 < R) (k : ℕ) (hcore : AdmissibleRadius μ (latticeRadius R k / 8))
    (z : (supportLatticeNets μ R hR k).points)
    (Good : SupportCellDescendant μ R hR k z → Prop)
    (S : SupportCellDescendant μ R hR k z → AffineSubspace ℝ (Ambient d))
    (hS : ∀ i, IsAffineNPlane n (S i)) (ε : ℝ) (hε : 0 < ε)
    (hεfine : ε ≤ 1 / 281474976710656) (hsmall : activeProjectionError d ε ≤ 1 / 128)
    (hfit : ∀ i, activeRegionCell Good i →
      bilateralPlaneError μ i.center (1024 * i.radius) (S i) < ε)
    (f : S (supportCellRoot μ R hR k z) → Ambient d)
    (hmodel : IsActiveRegionLimitModel μ R hR k z Good S hS ε f)
    (p : Ambient d) (hp : p ∈ Set.range f) (r : ℝ) (hr : 0 < r) :
    activeRegionAllRadiusLowerAreaConstant n C G * (ENNReal.ofReal r) ^ n ≤
      (μH[(n : ℝ)] : Measure (Ambient d)) (Set.range f ∩ closedBall p r) := by
  by_cases hlarge : 8 * latticeRadius R k ≤ r
  · have harea := active_region_limit_large_radius_ball_area_ge hn μ R hR k z Good S hS ε
      (by linarith) f hmodel p hp r hr hlarge
    exact (mul_le_mul_left (min_le_right _ _) _).trans harea
  · have harea := active_region_limit_small_radius_ball_area_ge μ C G hC hG hg hlower R hR k hcore
      z Good S hS ε hε hεfine hsmall hfit f hmodel p hp (r / 8) (by positivity) (by linarith)
    have hsub : Set.range f ∩ closedBall p (r / 8) ⊆ Set.range f ∩ closedBall p r := by
      intro x hx
      refine ⟨hx.1, ?_⟩
      have hx' : dist x p ≤ r / 8 := hx.2
      change dist x p ≤ r
      linarith
    have heq : activeRegionSmallRadiusLowerAreaConstant n C G * (ENNReal.ofReal (r / 8)) ^ n =
        (activeRegionSmallRadiusLowerAreaConstant n C G * (ENNReal.ofReal (1 / 8 : ℝ)) ^ n) *
          (ENNReal.ofReal r) ^ n := by
      rw [show r / 8 = (1 / 8) * r by ring,
        ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 8), mul_pow]
      exact (mul_assoc _ _ _).symm
    rw [heq] at harea
    exact ((mul_le_mul_left (min_le_left _ _) _).trans harea).trans (measure_mono hsub)

end

end RieszRectifiability

end OAI
