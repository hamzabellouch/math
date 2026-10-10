import Mathlib
import OAI.Analysis.RieszRectifiability.Restart.ActiveRegionExteriorPlane
import OAI.Analysis.RieszRectifiability.Flatness.AffineExteriorDisk

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped NNReal ENNReal

def activeRegionLargeRadiusLowerAreaConstant (n : ℕ) : ℝ≥0∞ :=
  planeDiskLowerAreaConstant n 1 * (ENNReal.ofReal (1 / 8 : ℝ)) ^ n

theorem activeRegionLargeRadiusLowerAreaConstant_pos (n : ℕ) :
    0 < activeRegionLargeRadiusLowerAreaConstant n := by
  exact ENNReal.mul_pos (planeDiskLowerAreaConstant_pos n 1).ne' (by positivity)

theorem activeRegionLargeRadiusLowerAreaConstant_lt_top (n : ℕ) :
    activeRegionLargeRadiusLowerAreaConstant n < ⊤ := by
  exact ENNReal.mul_lt_top (planeDiskLowerAreaConstant_lt_top n 1 (by norm_num)) (by finiteness)

theorem active_region_limit_large_radius_ball_area_ge {n d : ℕ} (hn : 0 < n)
    (μ : Measure (Ambient d)) (R : ℝ) (hR : 0 < R) (k : ℕ)
    (z : (supportLatticeNets μ R hR k).points)
    (Good : SupportCellDescendant μ R hR k z → Prop)
    (S : SupportCellDescendant μ R hR k z → AffineSubspace ℝ (Ambient d))
    (hS : ∀ i, IsAffineNPlane n (S i)) (ε : ℝ) (hεtiny : ε ≤ 1 / 268435456)
    (f : S (supportCellRoot μ R hR k z) → Ambient d)
    (hmodel : IsActiveRegionLimitModel μ R hR k z Good S hS ε f)
    (p : Ambient d) (hp : p ∈ Set.range f)
    (r : ℝ) (hr : 0 < r) (hrlarge : 8 * latticeRadius R k ≤ r) :
    activeRegionLargeRadiusLowerAreaConstant n * (ENNReal.ofReal r) ^ n ≤
      (μH[(n : ℝ)] : Measure (Ambient d)) (Set.range f ∩ closedBall p r) := by
  obtain ⟨u, hu⟩ := hp
  have hr0 := latticeRadius_pos R hR k
  have hB : (17039360 * ε) / 63 ≤ 1 / 16 := by linarith
  have hBm := mul_le_mul_of_nonneg_right hB hr0.le
  have hnear : dist (u : Ambient d) p ≤ r / 8 := by
    have ht : dist (u : Ambient d) p ≤ ((17039360 * ε) / 63) * latticeRadius R k := by
      simpa only [activeRegionParameterMap, id_eq, Nat.add_zero, hu] using! hmodel.2.2.2.1 0 u
    linarith
  have hdim : 0 < Module.finrank ℝ (S (supportCellRoot μ R hR k z)).direction := by
    rw [(hS _).2]
    exact hn
  obtain ⟨a, g, _, hsep, hinto, hfar⟩ := exists_affine_exterior_disk
    (S (supportCellRoot μ R hR k z)) hdim p u (z : Ambient d) u.property r hr hnear
  have hsub : Set.range g ⊆ Set.range f ∩ closedBall p r := by
    intro x hx
    have hxS := (hinto hx).1
    have hfix := active_region_limit_fixes_exterior_plane μ R hR k z Good S hS ε f hmodel
      ⟨x, hxS⟩ (by change 3 * latticeRadius R k ≤ dist x (z : Ambient d); linarith [hfar x hx])
    exact ⟨⟨⟨x, hxS⟩, hfix⟩, (hinto hx).2⟩
  have harea := (plane_disk_antilipschitz_range_hausdorffMeasure_ge
    (S (supportCellRoot μ R hR k z)).direction (hS _).2 a (r / 8) (by positivity)
    1 (by norm_num) g hsep).trans (measure_mono hsub)
  have heq : planeDiskLowerAreaConstant n 1 * (ENNReal.ofReal (r / 8)) ^ n =
      activeRegionLargeRadiusLowerAreaConstant n * (ENNReal.ofReal r) ^ n := by
    rw [show r / 8 = (1 / 8) * r by ring,
      ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 8), mul_pow]
    exact (mul_assoc _ _ _).symm
  rwa [heq] at harea

end

end RieszRectifiability

end OAI
