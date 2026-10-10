import Mathlib
import OAI.Analysis.RieszRectifiability.Restart.ActiveRegionZeroSetArea
import OAI.Analysis.RieszRectifiability.Restart.ActiveRegionLargeScaleArea
import OAI.Analysis.RieszRectifiability.Restart.ActiveRegionSmallScaleArea
import OAI.Analysis.RieszRectifiability.Surfaces.OriginalTopAreaCharges

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped NNReal ENNReal

def activeRegionUniformAreaConstant (n d : ℕ) (C G : ℝ) : ℝ≥0∞ :=
  activeRegionZeroAreaConstant n C +
    activeRegionSmallScaleAreaConstant n d C * enlargedTopMassConstant n C G +
    activeRegionLargeAreaConstant n d * ENNReal.ofReal (C * 8 ^ n)

theorem activeRegionUniformAreaConstant_lt_top (n d : ℕ) (C G : ℝ) :
    activeRegionUniformAreaConstant n d C G < ⊤ := by
  exact ENNReal.add_lt_top.mpr ⟨ENNReal.add_lt_top.mpr
    ⟨activeRegionZeroAreaConstant_lt_top n C,
      ENNReal.mul_lt_top (activeRegionSmallScaleAreaConstant_lt_top n d C)
        (enlargedTopMassConstant_lt_top n C G)⟩,
    ENNReal.mul_lt_top (activeRegionLargeAreaConstant_lt_top n d) ENNReal.ofReal_lt_top⟩

theorem active_region_limit_area_le_original_top {n d : ℕ}
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
    (hmodel : IsActiveRegionLimitModel μ R hR k z Good S hS ε f) :
    (μH[(n : ℝ)] : Measure (Ambient d))
      (Set.range f ∩ closedBall (z : Ambient d) (2 * latticeRadius R k)) ≤
      activeRegionUniformAreaConstant n d C G * μ (cleanSupportCell μ R hR k z) := by
  let D := cellRegionStoppingScale μ R hR k z Good
  let Z := cellRegionZeroSet μ R hR k z Good
  let T := Set.range f ∩ closedBall (z : Ambient d) (2 * latticeRadius R k)
  let A := T ∩ {x | 0 < D x ∧ D x < latticeRadius R (k + 1)}
  let B := closedBall (z : Ambient d) (2 * latticeRadius R k) ∩
    {x | latticeRadius R (k + 1) ≤ D x}
  have hz := active_region_zero_set_area_le_top μ C G hC hG hg hlower R hR k hcore z Good
  have hs := active_region_small_positive_scale_area_le μ C hC hlower R hR k hcore z Good S hS
    ε hε hεfine hsmall hfit f hmodel A (fun _ hx => hx.1) (fun _ hx => hx.2)
  have ht := enlarged_top_ball_mass_le_clean_top μ C G hC hG hg hlower R hR k hcore z
  have hs' := hs.trans (mul_le_mul_right ht (activeRegionSmallScaleAreaConstant n d C))
  have hl := active_region_large_scale_area_le μ R hR k z Good S hS ε hε.le (by linarith)
    hfit f hmodel B inter_subset_left (fun _ hx => hx.2)
  have hr := clean_top_radius_power_le_mass μ C G hC hG hg hlower R hR k hcore z
  have hl' := hl.trans (mul_le_mul_right hr (activeRegionLargeAreaConstant n d))
  have hcover : T ⊆ (Z ∪ A) ∪ (Set.range f ∩ B) := by
    intro x hx
    by_cases hzero : D x = 0
    · exact Or.inl (Or.inl hzero)
    · have hnonneg : 0 ≤ D x := cellRegionStoppingScale_nonneg μ R hR k z Good x
      have hpos : 0 < D x := by exact lt_of_le_of_ne hnonneg (Ne.symm hzero)
      by_cases hsmallx : D x < latticeRadius R (k + 1)
      · exact Or.inl (Or.inr ⟨hx, hpos, hsmallx⟩)
      · exact Or.inr ⟨hx.1, hx.2, le_of_not_gt hsmallx⟩
  calc
    _ ≤ (μH[(n : ℝ)] : Measure (Ambient d)) ((Z ∪ A) ∪ (Set.range f ∩ B)) := measure_mono hcover
    _ ≤ ((μH[(n : ℝ)] : Measure (Ambient d)) Z + (μH[(n : ℝ)] : Measure (Ambient d)) A) +
        (μH[(n : ℝ)] : Measure (Ambient d)) (Set.range f ∩ B) :=
      (measure_union_le _ _).trans (add_le_add (measure_union_le _ _) le_rfl)
    _ ≤ (activeRegionZeroAreaConstant n C * μ (cleanSupportCell μ R hR k z) +
        activeRegionSmallScaleAreaConstant n d C *
          (enlargedTopMassConstant n C G * μ (cleanSupportCell μ R hR k z))) +
        activeRegionLargeAreaConstant n d *
          (ENNReal.ofReal (C * 8 ^ n) * μ (cleanSupportCell μ R hR k z)) :=
      add_le_add (add_le_add hz hs') hl'
    _ = _ := by unfold activeRegionUniformAreaConstant; ring

end

end RieszRectifiability

end OAI
