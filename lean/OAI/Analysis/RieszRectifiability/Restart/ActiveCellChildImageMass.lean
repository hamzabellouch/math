import Mathlib
import OAI.Analysis.RieszRectifiability.Restart.SelectedStopChildGluing
import OAI.Analysis.RieszRectifiability.Restart.ActiveCellPieceSelection

namespace OAI

/-!
# Image-mass estimates for selected stopping cells

Pairwise disjointness controls the total mass omitted by child pieces. Combining
that bound with the active-cell representation estimates the mass still missing
from a glued image in terms of discarded surface area and child-cell losses.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal NNReal

def activeCellSelectedStopSet {d : ℕ} (μ : Measure (Ambient d))
    (R : ℝ) (hR : 0 < R) (k : ℕ)
    (z : (supportLatticeNets μ R hR k).points)
    (Good : SupportCellDescendant μ R hR k z → Prop)
    (q : SupportCellDescendant μ R hR k z) (E : Set (Ambient d)) :
    Set (SupportCellDescendant μ R hR k z) :=
  {i | i ∈ activeCellStopDescendants μ R hR k z Good q ∧
    ¬ Disjoint (closedBall i.center (i.radius / 32)) E}

theorem selected_stop_deficit_sum_le_cell_mass {d : ℕ}
    (μ : Measure (Ambient d)) (R : ℝ) (hR : 0 < R) (k : ℕ)
    (z : (supportLatticeNets μ R hR k).points)
    (Good : SupportCellDescendant μ R hR k z → Prop)
    (q : SupportCellDescendant μ R hR k z) (E : Set (Ambient d))
    (B : activeCellSelectedStopSet μ R hR k z Good q E → Set (Ambient d)) :
    (∑' i : activeCellSelectedStopSet μ R hR k z Good q E, μ (i.val.cell \ B i)) ≤ μ q.cell := by
  let := supportCellDescendant_countable μ R hR k z
  let F := activeCellSelectedStopSet μ R hR k z Good q E
  have hd : Pairwise (fun i j : F => Disjoint i.val.cell j.val.cell) := by
    intro i j hij
    exact cellRegionStops_pairwise_disjoint μ R hR k z Good i.property.1.1 j.property.1.1
      (fun heq => hij (Subtype.ext heq))
  have hm (i : F) : MeasurableSet i.val.cell :=
    cleanSupportCell_measurable μ R hR (k + i.val.depth) ⟨i.val.center, i.val.mem_net⟩
  calc
    _ ≤ ∑' i : F, μ i.val.cell := ENNReal.tsum_le_tsum (fun _ => measure_mono sdiff_subset)
    _ = μ (⋃ i : F, i.val.cell) := (measure_iUnion hd hm).symm
    _ ≤ μ q.cell := measure_mono (iUnion_subset (fun i => i.property.1.2.2))

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

theorem active_cell_mass_le_selected_image_add_losses
    (q : SupportCellDescendant μ R hR k z) (hq : activeRegionCell Good q)
    (E : Set (Ambient d))
    (B : activeCellSelectedStopSet μ R hR k z Good q E → Set (Ambient d))
    (T : Set (Ambient d))
    (hcover : ((cellRegionLimit μ R hR k z Good ∩ q.cell ∩ E) ∪
      ⋃ i : activeCellSelectedStopSet μ R hR k z Good q E, B i) ⊆ T) :
    μ q.cell ≤ μ (q.cell ∩ T) +
      (ENNReal.ofReal G + activeRegionStopMassAreaConstant n G) *
        (μH[(n : ℝ)] : Measure (Ambient d))
          ((Set.range f ∩ closedBall q.center (3 * q.radius)) \ E) +
      ∑' i : activeCellSelectedStopSet μ R hR k z Good q E, μ (i.val.cell \ B i) := by
  classical
  let := supportCellDescendant_countable μ R hR k z
  let F := activeCellSelectedStopSet μ R hR k z Good q E
  have hrep : activeCellRepresentedSet μ R hR k z Good q E ⊆
      (q.cell ∩ T) ∪ ⋃ i : F, i.val.cell \ B i := by
    intro x hx
    rcases hx with hp | hc
    · exact Or.inl ⟨hp.1.2, hcover (Or.inl hp)⟩
    · obtain ⟨i, hi⟩ := mem_iUnion.mp hc
      by_cases hB : x ∈ B i
      · exact Or.inl ⟨i.property.1.2.2 hi, hcover (Or.inr (mem_iUnion.mpr ⟨i, hB⟩))⟩
      · exact Or.inr (mem_iUnion.mpr ⟨i, hi, hB⟩)
  have hrepMass : μ (activeCellRepresentedSet μ R hR k z Good q E) ≤
      μ (q.cell ∩ T) + ∑' i : F, μ (i.val.cell \ B i) :=
    ((measure_mono hrep).trans (measure_union_le _ _)).trans
      (add_le_add le_rfl (measure_iUnion_le _))
  have hmass := active_cell_mass_le_represented_mass_add_discarded_area μ G hG hg R hR k z
    Good S hS ε hε hεfine hsmall hfit f hmodel q hq E
  exact (hmass.trans (add_le_add hrepMass le_rfl)).trans_eq (by ac_rfl)

theorem exists_active_cell_glued_chart_with_mass_losses
    (q : SupportCellDescendant μ R hR k z) (hq : activeRegionCell Good q)
    (E : Set (Ambient d)) (coord : Ambient d → Ambient n) (L : ℝ≥0) (hL : 1 ≤ L)
    (hcoord : ∀ x ∈ E, ∀ y ∈ E, dist x y ≤ (L : ℝ) * dist (coord x) (coord y))
    (hcoordBall : ∀ x ∈ E, coord x ∈ closedBall (0 : Ambient n) q.radius)
    (child : ∀ i : activeCellSelectedStopSet μ R hR k z Good q E,
      ball (0 : Ambient n) i.val.radius → Ambient d)
    (M : ℝ≥0) (hLip : ∀ i, LipschitzWith M (child i))
    (himage : ∀ i, Set.range (child i) ⊆ closedBall i.val.center (2 * i.val.radius)) :
    ∃ g : ball (0 : Ambient n) (2 * q.radius) → Ambient d,
      LipschitzWith (lipschitzExtensionConstant (Ambient d) *
        separatedPatchGluingConstant (M * (4 * (32 * L))) (32 * L) L) g ∧
      μ q.cell ≤ μ (q.cell ∩ Set.range g) +
        (ENNReal.ofReal G + activeRegionStopMassAreaConstant n G) *
          (μH[(n : ℝ)] : Measure (Ambient d))
            ((Set.range f ∩ closedBall q.center (3 * q.radius)) \ E) +
        ∑' i : activeCellSelectedStopSet μ R hR k z Good q E,
          μ (i.val.cell \ Set.range (child i)) := by
  classical
  let F := activeCellSelectedStopSet μ R hR k z Good q E
  have hx (i : F) : ∃ x : Ambient d, x ∈ closedBall i.val.center (i.val.radius / 32) ∧ x ∈ E :=
    Set.not_disjoint_iff.mp i.property.2
  choose x hxcore hxE using hx
  have hradius (i : F) : i.val.radius ≤ q.radius :=
    latticeRadius_antitone R hR.le (Nat.add_le_add_left i.property.1.2.1.le k)
  obtain ⟨g, hgLip, hcover⟩ := exists_ball_lipschitz_cover_of_stop_children_and_survivors
    μ R hR k z Good E coord L hL hcoord q.radius q.radius_pos hcoordBall F
    (fun _ hi => hi.1.1) x hxcore hxE hradius child M hLip himage
  refine ⟨g, hgLip, ?_⟩
  apply active_cell_mass_le_selected_image_add_losses μ G hG hg R hR k z Good S hS
    ε hε hεfine hsmall hfit f hmodel q hq E (fun i => Set.range (child i)) (Set.range g)
  intro y hy
  rcases hy with hp | hc
  · exact hcover (Or.inl ⟨hp.1.1, hp.2⟩)
  · exact hcover (Or.inr hc)

end

end RieszRectifiability

end OAI
