import Mathlib
import OAI.Analysis.RieszRectifiability.Restart.ActiveRegionFiniteDistortion
import OAI.Analysis.RieszRectifiability.Surfaces.LipschitzChartLift

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped NNReal

variable {n d : ℕ} (μ : Measure (Ambient d)) (R : ℝ) (hR : 0 < R) (k : ℕ)
  (z : (supportLatticeNets μ R hR k).points)
  (Good : SupportCellDescendant μ R hR k z → Prop)
  (S : SupportCellDescendant μ R hR k z → AffineSubspace ℝ (Ambient d))
  (hS : ∀ i, IsAffineNPlane n (S i)) (ε : ℝ) (hε : 0 < ε)
  (hεtiny : ε ≤ 1 / 268435456) (hsmall : activeProjectionError d ε ≤ 1 / 128)
  (hfit : ∀ i, activeRegionCell Good i →
    bilateralPlaneError μ i.center (1024 * i.radius) (S i) < ε)

include hS hε hεtiny hsmall hfit

theorem activeRegionParameterMap_antilipschitz (t : ℕ) :
    AntilipschitzWith ((4 : ℝ≥0) ^ t)
      (fun u : S (supportCellRoot μ R hR k z) =>
        activeRegionParameterMap μ R hR k z Good S hS t u) := by
  apply AntilipschitzWith.of_le_mul_dist
  intro u v
  have h := (activeRegionParameterMap_dist_bounds μ R hR k z Good S hS
    ε hε hεtiny hsmall hfit t u v).1
  have hm := mul_le_mul_of_nonneg_left h (pow_nonneg (by norm_num : (0 : ℝ) ≤ 4) t)
  have hid : (4 : ℝ) ^ t * ((1 / 4 : ℝ) ^ t * dist u v) = dist u v := by
    rw [← mul_assoc, ← mul_pow]
    norm_num
  rw [hid] at hm
  simpa only [NNReal.coe_pow, NNReal.coe_ofNat] using! hm

theorem exists_active_region_finite_chart_lift {X : Type*} [MetricSpace X]
    (t : ℕ) (g : X → Ambient d) (L : ℝ≥0) (hg : LipschitzWith L g)
    (hinto : Set.range g ⊆ activeRegionSurface μ R hR k z Good S hS t) :
    ∃ h : X → S (supportCellRoot μ R hR k z),
      LipschitzWith ((4 : ℝ≥0) ^ t * L) h ∧
      ∀ x, activeRegionParameterMap μ R hR k z Good S hS t (h x) = g x := by
  apply exists_lipschitz_lift_of_antilipschitz
    (fun u : S (supportCellRoot μ R hR k z) =>
      activeRegionParameterMap μ R hR k z Good S hS t u) ((4 : ℝ≥0) ^ t)
    (activeRegionParameterMap_antilipschitz μ R hR k z Good S hS ε hε hεtiny hsmall hfit t)
    g L hg
  rintro _ ⟨x, rfl⟩
  have hx := hinto ⟨x, rfl⟩
  rw [activeRegionSurface_eq_image] at hx
  obtain ⟨u, hu, heq⟩ := hx
  exact ⟨⟨u, hu⟩, heq⟩

end

end RieszRectifiability

end OAI
