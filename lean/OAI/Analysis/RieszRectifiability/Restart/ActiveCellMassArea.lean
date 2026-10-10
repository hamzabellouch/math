import Mathlib
import OAI.Analysis.RieszRectifiability.Restart.ActiveLevelOriginalMass
import OAI.Analysis.RieszRectifiability.Restart.ActiveRegionStopMassArea
import OAI.Analysis.RieszRectifiability.Foundations.GrowthHausdorffDomination

namespace OAI

/-!
# Active-cell mass controlled by limit-model area

An active cell splits into its limiting region and a countable family of stopping
descendants. Hausdorff domination on the limiting region and the stopping-core
mass estimate bound its original measure by nearby area of the limit model.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal

variable {n d : ℕ} (μ : Measure (Ambient d)) (G : ℝ) (hG : 0 < G)
  (hg : GlobalUpperGrowth n G μ) (R : ℝ) (hR : 0 < R) (k : ℕ)
  (z : (supportLatticeNets μ R hR k).points)
  (Good : SupportCellDescendant μ R hR k z → Prop)
  (S : SupportCellDescendant μ R hR k z → AffineSubspace ℝ (Ambient d))
  (hS : ∀ i, IsAffineNPlane n (S i)) (ε : ℝ) (hε : 0 < ε)
  (hεfine : ε ≤ 1 / 281474976710656) (hsmall : activeProjectionError d ε ≤ 1 / 128)
  (hfit : ∀ i, activeRegionCell Good i →
    bilateralPlaneError μ i.center (1024 * i.radius) (S i) < ε)
  (f : S (supportCellRoot μ R hR k z) → Ambient d)
  (hmodel : IsActiveRegionLimitModel μ R hR k z Good S hS ε f)

include hG hg hε hεfine hsmall hfit hmodel

theorem active_cell_original_mass_le_limit_area
    (q : SupportCellDescendant μ R hR k z) (hq : activeRegionCell Good q) :
    μ q.cell ≤ (ENNReal.ofReal G + activeRegionStopMassAreaConstant n G) *
      (μH[(n : ℝ)] : Measure (Ambient d)) (Set.range f ∩ closedBall q.center (3 * q.radius)) := by
  let := supportCellDescendant_countable μ R hR k z
  let F : Set (SupportCellDescendant μ R hR k z) :=
    {i | i ∈ cellRegionStops μ R hR k z Good ∧ q.depth < i.depth ∧ i.cell ⊆ q.cell}
  let A := cellRegionLimit μ R hR k z Good ∩ q.cell
  let Ω := closedBall q.center (3 * q.radius)
  have hcover : q.cell ⊆ A ∪ ⋃ i : F, i.val.cell := by
    intro x hx
    by_cases hs : x ∈ cellRegionLimit μ R hR k z Good
    · exact Or.inl ⟨hs, hx⟩
    obtain ⟨i, hi, hxi⟩ := exists_first_failing_cell μ R hR k z Good x (q.cell_subset_top hx) hs
    have hdepth : q.depth < i.depth := by
      by_contra hn
      have hid : i.depth ≤ q.depth := le_of_not_gt hn
      exact hi.1 (hq i hid (q.cell_nested_of_common_point i hid x hx hxi))
    have hisub := i.cell_nested_of_common_point q hdepth.le x hxi hx
    exact Or.inr (mem_iUnion.mpr ⟨⟨i, hi, hdepth, hisub⟩, hxi⟩)
  have hsub : A ⊆ Set.range f ∩ Ω := by
    intro x hx
    refine ⟨hmodel.2.2.2.2.2.1 hx.1, ?_⟩
    have h := q.dist_center_of_mem x hx.2
    change dist x q.center ≤ 3 * q.radius
    have hrq := q.radius_pos
    linarith
  have hsurv : μ A ≤ ENNReal.ofReal G *
      (μH[(n : ℝ)] : Measure (Ambient d)) (Set.range f ∩ Ω) := by
    have h := global_growth_le_hausdorffMeasure μ G hG hg A
    simp only [Measure.smul_apply, smul_eq_mul] at h
    exact h.trans (mul_le_mul_right (measure_mono hsub) _)
  have hΩ : ∀ i ∈ F, closedBall i.center (i.radius / 32) ⊆ Ω := by
    intro i hi x hx
    have hnear := q.dist_center_of_mem i.center (hi.2.2 i.center_mem_cell)
    have hrad : i.radius ≤ q.radius :=
      latticeRadius_antitone R hR.le (Nat.add_le_add_left hi.2.1.le k)
    have hb : dist x i.center ≤ i.radius / 32 := hx
    have ht := dist_triangle x i.center q.center
    have hrq := q.radius_pos
    change dist x q.center ≤ 3 * q.radius
    linarith
  have hstops := active_region_stop_subfamily_mass_le_area μ G hg R hR k z Good S hS
    ε hε hεfine hsmall hfit f hmodel F (fun _ hi => hi.1)
    (fun _ hi => lt_of_le_of_lt (Nat.zero_le q.depth) hi.2.1) Ω hΩ
  calc
    _ ≤ μ (A ∪ ⋃ i : F, i.val.cell) := measure_mono hcover
    _ ≤ μ A + μ (⋃ i : F, i.val.cell) := measure_union_le _ _
    _ ≤ μ A + ∑' i : F, μ i.val.cell := add_le_add le_rfl (measure_iUnion_le _)
    _ ≤ ENNReal.ofReal G * (μH[(n : ℝ)] : Measure (Ambient d)) (Set.range f ∩ Ω) +
        activeRegionStopMassAreaConstant n G *
          (μH[(n : ℝ)] : Measure (Ambient d)) (Set.range f ∩ Ω) := add_le_add hsurv hstops
    _ = _ := (add_mul _ _ _).symm

theorem active_cell_radius_power_le_limit_area
    (C : ℝ) (hC : 0 < C)
    (hlower : ∀ x ∈ μ.support, ∀ r : ℝ, AdmissibleRadius μ r →
      ENNReal.ofReal (r ^ n / C) ≤ μ (ball x r))
    (hcore : AdmissibleRadius μ (latticeRadius R k / 8))
    (q : SupportCellDescendant μ R hR k z) (hq : activeRegionCell Good q) :
    (ENNReal.ofReal q.radius) ^ n ≤
      (ENNReal.ofReal (C * 8 ^ n) * (ENNReal.ofReal G + activeRegionStopMassAreaConstant n G)) *
        (μH[(n : ℝ)] : Measure (Ambient d)) (Set.range f ∩ closedBall q.center (3 * q.radius)) := by
  have hmass := SupportCellDescendant.radius_power_le_mass μ C G hC hG hg hlower R hR k hcore z q
  have harea := active_cell_original_mass_le_limit_area μ G hG hg R hR k z Good S hS
    ε hε hεfine hsmall hfit f hmodel q hq
  exact (hmass.trans (mul_le_mul_right harea _)).trans_eq (mul_assoc _ _ _).symm

end

end RieszRectifiability

end OAI
