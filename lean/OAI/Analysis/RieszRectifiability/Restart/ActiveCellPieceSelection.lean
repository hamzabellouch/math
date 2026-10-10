import Mathlib
import OAI.Analysis.RieszRectifiability.Restart.ActiveRegionPieceLoss

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal

def activeCellStopDescendants {d : ℕ} (μ : Measure (Ambient d))
    (R : ℝ) (hR : 0 < R) (k : ℕ)
    (z : (supportLatticeNets μ R hR k).points)
    (Good : SupportCellDescendant μ R hR k z → Prop)
    (q : SupportCellDescendant μ R hR k z) : Set (SupportCellDescendant μ R hR k z) :=
  {i | i ∈ cellRegionStops μ R hR k z Good ∧ q.depth < i.depth ∧ i.cell ⊆ q.cell}

theorem active_cell_covered_by_survivors_and_deeper_stops {d : ℕ}
    (μ : Measure (Ambient d)) (R : ℝ) (hR : 0 < R) (k : ℕ)
    (z : (supportLatticeNets μ R hR k).points)
    (Good : SupportCellDescendant μ R hR k z → Prop)
    (q : SupportCellDescendant μ R hR k z) (hq : activeRegionCell Good q) :
    q.cell ⊆ (cellRegionLimit μ R hR k z Good ∩ q.cell) ∪
      ⋃ i : activeCellStopDescendants μ R hR k z Good q, i.val.cell := by
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

theorem descendant_small_core_subset_cell_enlargement {d : ℕ}
    (μ : Measure (Ambient d)) (R : ℝ) (hR : 0 < R) (k : ℕ)
    (z : (supportLatticeNets μ R hR k).points)
    (q i : SupportCellDescendant μ R hR k z)
    (hdepth : q.depth ≤ i.depth) (hsub : i.cell ⊆ q.cell) :
    closedBall i.center (i.radius / 32) ⊆ closedBall q.center (3 * q.radius) := by
  intro x hx
  have hnear := q.dist_center_of_mem i.center (hsub i.center_mem_cell)
  have hrad : i.radius ≤ q.radius :=
    latticeRadius_antitone R hR.le (Nat.add_le_add_left hdepth k)
  have hb : dist x i.center ≤ i.radius / 32 := hx
  have ht := dist_triangle x i.center q.center
  have hrq := q.radius_pos
  change dist x q.center ≤ 3 * q.radius
  linarith

def activeCellRepresentedSet {d : ℕ} (μ : Measure (Ambient d))
    (R : ℝ) (hR : 0 < R) (k : ℕ)
    (z : (supportLatticeNets μ R hR k).points)
    (Good : SupportCellDescendant μ R hR k z → Prop)
    (q : SupportCellDescendant μ R hR k z) (E : Set (Ambient d)) : Set (Ambient d) :=
  (cellRegionLimit μ R hR k z Good ∩ q.cell ∩ E) ∪
    ⋃ i : {i : SupportCellDescendant μ R hR k z //
      i ∈ activeCellStopDescendants μ R hR k z Good q ∧
        ¬ Disjoint (closedBall i.center (i.radius / 32)) E}, i.val.cell

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

theorem active_cell_remainder_mass_le_discarded_area
    (q : SupportCellDescendant μ R hR k z) (hq : activeRegionCell Good q)
    (E : Set (Ambient d)) :
    μ (q.cell \ activeCellRepresentedSet μ R hR k z Good q E) ≤
      (ENNReal.ofReal G + activeRegionStopMassAreaConstant n G) *
        (μH[(n : ℝ)] : Measure (Ambient d))
          ((Set.range f ∩ closedBall q.center (3 * q.radius)) \ E) := by
  classical
  let F := activeCellStopDescendants μ R hR k z Good q
  let Ω := closedBall q.center (3 * q.radius)
  have hloc : ∀ i ∈ F, closedBall i.center (i.radius / 32) ⊆ Ω := by
    intro i hi
    exact descendant_small_core_subset_cell_enlargement μ R hR k z q i hi.2.1.le hi.2.2
  have hcover : q.cell \ activeCellRepresentedSet μ R hR k z Good q E ⊆
      ((cellRegionLimit μ R hR k z Good ∩ Ω) \ E) ∪
      ⋃ i : {i : SupportCellDescendant μ R hR k z //
        i ∈ F ∧ Disjoint (closedBall i.center (i.radius / 32)) E}, i.val.cell := by
    intro x hx
    have hxnot := hx.2
    change x ∉ (cellRegionLimit μ R hR k z Good ∩ q.cell ∩ E) ∪ _ at hxnot
    rcases active_cell_covered_by_survivors_and_deeper_stops μ R hR k z Good q hq hx.1 with hs | ht
    · refine Or.inl ⟨⟨hs.1, ?_⟩, ?_⟩
      · have hd := q.dist_center_of_mem x hx.1
        have hr := q.radius_pos
        change dist x q.center ≤ 3 * q.radius
        linarith
      · exact fun hE => hxnot (Or.inl ⟨hs, hE⟩)
    · obtain ⟨i, hi⟩ := mem_iUnion.mp ht
      have hd : Disjoint (closedBall i.val.center (i.val.radius / 32)) E := by
        by_contra hn
        exact hxnot (Or.inr (mem_iUnion.mpr ⟨⟨i.val, i.property, hn⟩, hi⟩))
      exact Or.inr (mem_iUnion.mpr ⟨⟨i.val, i.property, hd⟩, hi⟩)
  exact (measure_mono hcover).trans
    (active_region_unrepresented_mass_le_discarded_area μ G hg R hR k z Good S hS
      ε hε hεfine hsmall hfit f hmodel hG F (fun _ hi => hi.1)
      (fun _ hi => lt_of_le_of_lt (Nat.zero_le q.depth) hi.2.1) Ω E hloc)

theorem active_cell_mass_le_represented_mass_add_discarded_area
    (q : SupportCellDescendant μ R hR k z) (hq : activeRegionCell Good q)
    (E : Set (Ambient d)) :
    μ q.cell ≤ μ (activeCellRepresentedSet μ R hR k z Good q E) +
      (ENNReal.ofReal G + activeRegionStopMassAreaConstant n G) *
        (μH[(n : ℝ)] : Measure (Ambient d))
          ((Set.range f ∩ closedBall q.center (3 * q.radius)) \ E) := by
  classical
  let A := activeCellRepresentedSet μ R hR k z Good q E
  have hcover : q.cell ⊆ A ∪ (q.cell \ A) := by
    intro x hx
    by_cases hA : x ∈ A
    · exact Or.inl hA
    · exact Or.inr ⟨hx, hA⟩
  exact ((measure_mono hcover).trans (measure_union_le _ _)).trans
    (add_le_add le_rfl (active_cell_remainder_mass_le_discarded_area μ G hG hg R hR k z Good S hS
      ε hε hεfine hsmall hfit f hmodel q hq E))

end

end RieszRectifiability

end OAI
