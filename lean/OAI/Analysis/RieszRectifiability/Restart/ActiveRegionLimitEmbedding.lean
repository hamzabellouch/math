import Mathlib
import OAI.Analysis.RieszRectifiability.Restart.ActiveRegionLimitModel
import OAI.Analysis.RieszRectifiability.Restart.ActiveRegionFiniteDistortion

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology

variable {n d : ℕ} (μ : Measure (Ambient d)) (R : ℝ) (hR : 0 < R) (k : ℕ)
  (z : (supportLatticeNets μ R hR k).points)
  (Good : SupportCellDescendant μ R hR k z → Prop)
  (S : SupportCellDescendant μ R hR k z → AffineSubspace ℝ (Ambient d))
  (hS : ∀ i, IsAffineNPlane n (S i)) (ε : ℝ) (hε : 0 < ε)
  (hεtiny : ε ≤ 1 / 268435456) (hsmall : activeProjectionError d ε ≤ 1 / 128)
  (hfit : ∀ i, activeRegionCell Good i →
    bilateralPlaneError μ i.center (1024 * i.radius) (S i) < ε)
  (f : S (supportCellRoot μ R hR k z) → Ambient d)
  (hmodel : IsActiveRegionLimitModel μ R hR k z Good S hS ε f)

include hS hε hεtiny hsmall hfit hmodel

theorem active_region_limit_injective : Function.Injective f := by
  intro u v huv
  let B := (17039360 * ε) / 63
  have htail : ∀ t (w : S (supportCellRoot μ R hR k z)),
      dist (activeRegionParameterMap μ R hR k z Good S hS t w) (f w) ≤
      B * latticeRadius R (k + t) := hmodel.2.2.2.1
  have hbound : ∀ t : ℕ, dist u v ≤
      (2 * B * latticeRadius R k) * (1 / 16 : ℝ) ^ t := by
    intro t
    have hfinite := activeRegionParameterMap_dist_bounds μ R hR k z Good S hS
      ε hε hεtiny hsmall hfit t u v
    have hpair : dist (activeRegionParameterMap μ R hR k z Good S hS t u)
        (activeRegionParameterMap μ R hR k z Good S hS t v) ≤
        2 * B * latticeRadius R (k + t) := by
      have ht := dist_triangle (activeRegionParameterMap μ R hR k z Good S hS t u)
        (f u) (activeRegionParameterMap μ R hR k z Good S hS t v)
      have hv : dist (f u) (activeRegionParameterMap μ R hR k z Good S hS t v) ≤
          B * latticeRadius R (k + t) := by rw [huv, dist_comm]; exact htail t v
      linarith [htail t u]
    have hm := mul_le_mul_of_nonneg_left (hfinite.1.trans hpair)
      (pow_nonneg (by norm_num : (0 : ℝ) ≤ 4) t)
    have hleft : (4 : ℝ) ^ t * ((1 / 4 : ℝ) ^ t * dist u v) = dist u v := by
      rw [← mul_assoc, ← mul_pow]
      norm_num
    have hright : (4 : ℝ) ^ t * (2 * B * latticeRadius R (k + t)) =
        (2 * B * latticeRadius R k) * (1 / 16 : ℝ) ^ t := by
      rw [latticeRadius_add]
      calc
        _ = (2 * B * latticeRadius R k) * ((4 : ℝ) ^ t * (1 / 64 : ℝ) ^ t) := by ring
        _ = _ := by rw [← mul_pow]; norm_num
    rw [hleft, hright] at hm
    exact hm
  have hlim : Tendsto (fun t : ℕ => (2 * B * latticeRadius R k) * (1 / 16 : ℝ) ^ t)
      atTop (𝓝 0) := by
    simpa only [mul_zero] using!
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 16)
        (by norm_num : (1 / 16 : ℝ) < 1)).const_mul (2 * B * latticeRadius R k)
  exact dist_eq_zero.mp (le_antisymm (ge_of_tendsto hlim (Eventually.of_forall hbound)) dist_nonneg)

theorem active_region_limit_isClosedEmbedding : IsClosedEmbedding f :=
  IsClosedEmbedding.of_continuous_injective_isClosedMap hmodel.1
    (active_region_limit_injective μ R hR k z Good S hS ε hε hεtiny hsmall hfit f hmodel)
    hmodel.2.1.isClosedMap

end

end RieszRectifiability

end OAI
