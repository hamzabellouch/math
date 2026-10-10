import Mathlib
import OAI.Analysis.RieszRectifiability.Restart.ActiveRegionStopMassArea
import OAI.Analysis.RieszRectifiability.Foundations.GrowthHausdorffDomination

namespace OAI

/-!
# Mass lost outside an active-region piece

Stopping cells whose inner balls miss a chosen piece are charged to discarded
surface area. Combining this estimate with Hausdorff domination bounds the mass
of both the uncovered limit set and the unrepresented stopping cells.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal

variable {n d : ℕ} (μ : Measure (Ambient d)) (G : ℝ) (hg : GlobalUpperGrowth n G μ)
  (R : ℝ) (hR : 0 < R) (k : ℕ)
  (z : (supportLatticeNets μ R hR k).points)
  (Good : SupportCellDescendant μ R hR k z → Prop)
  (S : SupportCellDescendant μ R hR k z → AffineSubspace ℝ (Ambient d))
  (hS : ∀ i, IsAffineNPlane n (S i)) (ε : ℝ) (hε : 0 < ε)
  (hεfine : ε ≤ 1 / 281474976710656) (hsmall : activeProjectionError d ε ≤ 1 / 128)
  (hfit : ∀ i, activeRegionCell Good i →
    bilateralPlaneError μ i.center (1024 * i.radius) (S i) < ε)
  (f : S (supportCellRoot μ R hR k z) → Ambient d)
  (hmodel : IsActiveRegionLimitModel μ R hR k z Good S hS ε f)

include hg hε hεfine hsmall hfit hmodel

theorem active_region_missed_stop_mass_le_discarded_area
    (F : Set (SupportCellDescendant μ R hR k z))
    (hF : F ⊆ cellRegionStops μ R hR k z Good) (hdepth : ∀ i ∈ F, 0 < i.depth)
    (Ω E : Set (Ambient d)) (hΩ : ∀ i ∈ F, closedBall i.center (i.radius / 32) ⊆ Ω) :
    (∑' i : {i : SupportCellDescendant μ R hR k z //
      i ∈ F ∧ Disjoint (closedBall i.center (i.radius / 32)) E}, μ i.val.cell) ≤
      activeRegionStopMassAreaConstant n G *
        (μH[(n : ℝ)] : Measure (Ambient d)) ((Set.range f ∩ Ω) \ E) := by
  let B : Set (SupportCellDescendant μ R hR k z) :=
    {i | i ∈ F ∧ Disjoint (closedBall i.center (i.radius / 32)) E}
  have hB : B ⊆ cellRegionStops μ R hR k z Good := fun _ hi => hF hi.1
  have hloc : ∀ i ∈ B, closedBall i.center (i.radius / 32) ⊆ Ω \ E := by
    intro i hi x hx
    exact ⟨hΩ i hi.1 hx, fun hE => Set.disjoint_left.mp hi.2 hx hE⟩
  have h := active_region_stop_subfamily_mass_le_area μ G hg R hR k z Good S hS
    ε hε hεfine hsmall hfit f hmodel B hB (fun i hi => hdepth i hi.1) (Ω \ E) hloc
  have heq : Set.range f ∩ (Ω \ E) = (Set.range f ∩ Ω) \ E := by ext x; simp only [mem_inter_iff, mem_sdiff]; tauto
  rwa [heq] at h

theorem active_region_unrepresented_mass_le_discarded_area
    (hG : 0 < G)
    (F : Set (SupportCellDescendant μ R hR k z))
    (hF : F ⊆ cellRegionStops μ R hR k z Good) (hdepth : ∀ i ∈ F, 0 < i.depth)
    (Ω E : Set (Ambient d)) (hΩ : ∀ i ∈ F, closedBall i.center (i.radius / 32) ⊆ Ω) :
    μ (((cellRegionLimit μ R hR k z Good ∩ Ω) \ E) ∪
      ⋃ i : {i : SupportCellDescendant μ R hR k z //
        i ∈ F ∧ Disjoint (closedBall i.center (i.radius / 32)) E}, i.val.cell) ≤
      (ENNReal.ofReal G + activeRegionStopMassAreaConstant n G) *
        (μH[(n : ℝ)] : Measure (Ambient d)) ((Set.range f ∩ Ω) \ E) := by
  let := supportCellDescendant_countable μ R hR k z
  let A := (cellRegionLimit μ R hR k z Good ∩ Ω) \ E
  let B := {i : SupportCellDescendant μ R hR k z |
    i ∈ F ∧ Disjoint (closedBall i.center (i.radius / 32)) E}
  have hsub : A ⊆ (Set.range f ∩ Ω) \ E := by
    intro x hx
    exact ⟨⟨hmodel.2.2.2.2.2.1 hx.1.1, hx.1.2⟩, hx.2⟩
  have hsurv : μ A ≤ ENNReal.ofReal G *
      (μH[(n : ℝ)] : Measure (Ambient d)) ((Set.range f ∩ Ω) \ E) := by
    have h := global_growth_le_hausdorffMeasure μ G hG hg A
    simp only [Measure.smul_apply, smul_eq_mul] at h
    exact h.trans (mul_le_mul_right (measure_mono hsub) _)
  have hstops := active_region_missed_stop_mass_le_discarded_area μ G hg R hR k z Good S hS
    ε hε hεfine hsmall hfit f hmodel F hF hdepth Ω E hΩ
  calc
    _ ≤ μ A + μ (⋃ i : B, i.val.cell) := measure_union_le _ _
    _ ≤ μ A + ∑' i : B, μ i.val.cell := add_le_add le_rfl (measure_iUnion_le _)
    _ ≤ ENNReal.ofReal G * (μH[(n : ℝ)] : Measure (Ambient d)) ((Set.range f ∩ Ω) \ E) +
        activeRegionStopMassAreaConstant n G *
          (μH[(n : ℝ)] : Measure (Ambient d)) ((Set.range f ∩ Ω) \ E) := add_le_add hsurv hstops
    _ = _ := (add_mul _ _ _).symm

end

end RieszRectifiability

end OAI
