import Mathlib
import OAI.Analysis.RieszRectifiability.Restart.ActiveCellFinitePieceAssembly

namespace OAI

/-!
# Deficit bounds for active-cell chart assembly

The uncovered mass of an active cell splits into discarded parent surface area
and deficits of the selected stopping children. Gluing the parent pieces and
child charts preserves their covered sets and transfers this estimate to a
bounded ball chart, with the stated finite-piece Lipschitz constant.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped NNReal ENNReal

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

theorem active_cell_deficit_le_selected_losses
    (q : SupportCellDescendant μ R hR k z) (hq : activeRegionCell Good q)
    (E : Set (Ambient d))
    (B : activeCellSelectedStopSet μ R hR k z Good q E → Set (Ambient d))
    (T : Set (Ambient d))
    (hparent : cellRegionLimit μ R hR k z Good ∩ q.cell ∩ E ⊆ T)
    (hchild : ∀ i, i.val.cell ∩ B i ⊆ T) :
    μ (q.cell \ T) ≤
      (ENNReal.ofReal G + activeRegionStopMassAreaConstant n G) *
        (μH[(n : ℝ)] : Measure (Ambient d))
          ((Set.range f ∩ closedBall q.center (3 * q.radius)) \ E) +
      ∑' i : activeCellSelectedStopSet μ R hR k z Good q E, μ (i.val.cell \ B i) := by
  classical
  let := supportCellDescendant_countable μ R hR k z
  let F := activeCellSelectedStopSet μ R hR k z Good q E
  have hsub : q.cell \ T ⊆ (q.cell \ activeCellRepresentedSet μ R hR k z Good q E) ∪
      ⋃ i : F, i.val.cell \ B i := by
    intro x hx
    by_cases hrep : x ∈ activeCellRepresentedSet μ R hR k z Good q E
    · rcases hrep with hp | hc
      · exact (hx.2 (hparent hp)).elim
      · obtain ⟨i, hi⟩ := mem_iUnion.mp hc
        exact Or.inr (mem_iUnion.mpr ⟨i, hi, fun hb => hx.2 (hchild i ⟨hi, hb⟩)⟩)
    · exact Or.inl ⟨hx.1, hrep⟩
  have hmass : μ (q.cell \ T) ≤ μ (q.cell \ activeCellRepresentedSet μ R hR k z Good q E) +
      ∑' i : F, μ (i.val.cell \ B i) :=
    ((measure_mono hsub).trans (measure_union_le _ _)).trans
    (add_le_add le_rfl (measure_iUnion_le _))
  exact hmass.trans (add_le_add
    (active_cell_remainder_mass_le_discarded_area μ G hG hg R hR k z Good S hS
      ε hε hεfine hsmall hfit f hmodel q hq E) le_rfl)

theorem exists_active_cell_chart_with_deficit_bound
    (q : SupportCellDescendant μ R hR k z) (hq : activeRegionCell Good q)
    (E : Set (Ambient d)) (coord : Ambient d → Ambient n) (L : ℝ≥0) (hL : 1 ≤ L)
    (hcoord : ∀ x ∈ E, ∀ y ∈ E, dist x y ≤ (L : ℝ) * dist (coord x) (coord y))
    (hcoordBall : ∀ x ∈ E, coord x ∈ closedBall (0 : Ambient n) q.radius)
    (child : ∀ i : activeCellSelectedStopSet μ R hR k z Good q E,
      ball (0 : Ambient n) i.val.radius → Ambient d)
    (M : ℝ≥0) (hLip : ∀ i, LipschitzWith M (child i))
    (himage : ∀ i, Set.range (child i) ⊆ closedBall i.val.center (2 * i.val.radius)) :
    ∃ g : ball (0 : Ambient n) q.radius → Ambient d,
      LipschitzWith ((lipschitzExtensionConstant (Ambient d) *
        separatedPatchGluingConstant (M * (4 * (32 * L))) (32 * L) L) * 2) g ∧
      Set.range g ⊆ closedBall q.center (2 * q.radius) ∧
      (cellRegionLimit μ R hR k z Good ∩ q.cell ∩ E ⊆ Set.range g) ∧
      (∀ i, i.val.cell ∩ Set.range (child i) ⊆ Set.range g) ∧
      μ (q.cell \ Set.range g) ≤
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
  obtain ⟨g', hg'Lip, hg'Range, hpreserve⟩ := exists_bounded_normalized_ball_chart q.radius
    q.center (2 * q.radius) (by linarith [q.radius_pos]) g _ hgLip
  have hparent : cellRegionLimit μ R hR k z Good ∩ q.cell ∩ E ⊆ Set.range g' := by
    intro y hy
    apply hpreserve
    exact ⟨q.dist_center_of_mem y hy.1.2, hcover (Or.inl ⟨hy.1.1, hy.2⟩)⟩
  have hchild : ∀ i, i.val.cell ∩ Set.range (child i) ⊆ Set.range g' := by
    intro i y hy
    apply hpreserve
    exact ⟨q.dist_center_of_mem y (i.property.1.2.2 hy.1),
      hcover (Or.inr (mem_iUnion.mpr ⟨i, hy.2⟩))⟩
  exact ⟨g', hg'Lip, hg'Range, hparent, hchild,
    active_cell_deficit_le_selected_losses μ G hG hg R hR k z Good S hS
      ε hε hεfine hsmall hfit f hmodel q hq E (fun i => Set.range (child i))
      (Set.range g') hparent hchild⟩

theorem exists_active_cell_finite_piece_deficit_assembly (hn : 0 < n)
    (q : SupportCellDescendant μ R hR k z) (hq : activeRegionCell Good q)
    (N : ℕ) (D : Fin N → Set (Ambient n))
    (hD : ∀ j, D j ⊆ ball (0 : Ambient n) q.radius)
    (piece : Fin N → Ambient n → Ambient d) (P : ℝ≥0)
    (hpieceLip : ∀ j, LipschitzOnWith P (piece j) (D j))
    (hpieceImage : ∀ j, piece j '' D j ⊆ closedBall q.center (3 * q.radius))
    (E : Set (Ambient d)) (hE : E = ⋃ j : Fin N, piece j '' D j)
    (child : ∀ i : activeCellSelectedStopSet μ R hR k z Good q E,
      ball (0 : Ambient n) i.val.radius → Ambient d)
    (M : ℝ≥0) (hLip : ∀ i, LipschitzWith M (child i))
    (himage : ∀ i, Set.range (child i) ⊆ closedBall i.val.center (2 * i.val.radius)) :
    ∃ g : ball (0 : Ambient n) q.radius → Ambient d,
      LipschitzWith (activeCellFinitePieceAssemblyConstant d N P M) g ∧
      Set.range g ⊆ closedBall q.center (2 * q.radius) ∧
      (cellRegionLimit μ R hR k z Good ∩ q.cell ∩ E ⊆ Set.range g) ∧
      (∀ i, i.val.cell ∩ Set.range (child i) ⊆ Set.range g) ∧
      μ (q.cell \ Set.range g) ≤
        (ENNReal.ofReal G + activeRegionStopMassAreaConstant n G) *
          (μH[(n : ℝ)] : Measure (Ambient d))
            ((Set.range f ∩ closedBall q.center (3 * q.radius)) \ E) +
        ∑' i : activeCellSelectedStopSet μ R hR k z Good q E,
          μ (i.val.cell \ Set.range (child i)) := by
  obtain ⟨coord, hcoordBall, hcoord⟩ := exists_coordinates_of_finite_partial_charts hn N
    q.radius q.radius_pos q.center D hD piece P hpieceLip hpieceImage
  rw [← hE] at hcoordBall hcoord
  exact exists_active_cell_chart_with_deficit_bound μ G hG hg R hR k z Good S hS
    ε hε hεfine hsmall hfit f hmodel q hq E coord (finitePartialCoordinateConstant d N P)
    (finitePartialCoordinateConstant_ge_one d N P) hcoord hcoordBall child M hLip himage

end

end RieszRectifiability

end OAI
