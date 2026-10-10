import OAI.Geometry.IsometricImmersion.Estimates.RemainderAreaBudget
import OAI.Geometry.IsometricImmersion.Caps.CapCutoffRectangle

namespace OAI

noncomputable section
open Set Function
open scoped ContDiff Topology NNReal

namespace SmoothLocal.Flow
open SmoothLocal.Geometry SmoothLocal.Weighted SmoothLocal.ODE

structure LowerCapRectangle (bStar : ℝ) where
  left : ℝ
  right : ℝ
  bottom : ℝ
  top : ℝ
  left_gt : -2 < left
  right_lt : right < 2
  bottom_gt : -2 < bottom
  horizontal : left ≤ right
  vertical : bottom ≤ top
  top_lt : top < bStar
  ceiling_le : bStar ≤ 0

namespace LowerCapRectangle

variable {bStar : ℝ}

def region (r : LowerCapRectangle bStar) : Set Coord := closedRectangle r.left r.right r.bottom r.top

def image (r : LowerCapRectangle bStar) (Y : ℝ → ℝ → ℝ) : Set Coord := capChart Y '' r.region

theorem region_subset_domain (r : LowerCapRectangle bStar) : r.region ⊆ capChartDomain :=
  closedRectangle_subset_capChartDomain r.left_gt r.right_lt r.bottom_gt (by linarith [r.top_lt,r.ceiling_le])

def energyOuter (r : LowerCapRectangle bStar) : LowerCapRectangle bStar where
  left := capOuterLeft r.left
  right := capOuterRight r.right
  bottom := capOuterBottom r.bottom
  top := (r.top+bStar) / 2
  left_gt := (capOuterRectangle_edges r.left_gt r.right_lt r.bottom_gt).1
  right_lt := (capOuterRectangle_edges r.left_gt r.right_lt r.bottom_gt).2.2.2.2.2.1
  bottom_gt := (capOuterRectangle_edges r.left_gt r.right_lt r.bottom_gt).2.2.2.2.2.2.1
  horizontal := by
    obtain ⟨_,_,_,_,_,_,_,_,_,hL,hR⟩ := capOuterRectangle_edges r.left_gt r.right_lt r.bottom_gt
    linarith [r.horizontal]
  vertical := by
    obtain ⟨_,_,_,_,_,_,_,hB0,hB1,_,_⟩ := capOuterRectangle_edges r.left_gt r.right_lt r.bottom_gt
    linarith [r.vertical,r.top_lt]
  top_lt := by linarith [r.top_lt]
  ceiling_le := r.ceiling_le

theorem top_lt_energyOuter_top (r : LowerCapRectangle bStar) : r.top < r.energyOuter.top := by
  change r.top < (r.top+bStar)/2
  linarith [r.top_lt]

theorem region_subset_energyOuter (r : LowerCapRectangle bStar) : r.region ⊆ r.energyOuter.region := by
  obtain ⟨_,_,_,_,_,_,_,hB0,hB1,hL,hR⟩ := capOuterRectangle_edges r.left_gt r.right_lt r.bottom_gt
  intro p hp
  exact ⟨⟨by change capOuterLeft r.left ≤ p 0; linarith [hp.1.1],
    by change p 0 ≤ capOuterRight r.right; linarith [hp.1.2]⟩,
    ⟨by change capOuterBottom r.bottom ≤ p 1; linarith [hp.2.1],
      by change p 1 ≤ (r.top+bStar)/2; linarith [hp.2.2,r.top_lt]⟩⟩

def margin (r : LowerCapRectangle bStar) : ℝ :=
  min ((r.left+2)/2) (min ((2-r.right)/2) (min ((r.bottom+2)/2) ((bStar-r.top)/2)))

theorem margin_pos (r : LowerCapRectangle bStar) : 0 < r.margin := by
  unfold margin
  apply lt_min
  · linarith [r.left_gt]
  · apply lt_min
    · linarith [r.right_lt]
    · apply lt_min <;> linarith [r.bottom_gt,r.top_lt]

theorem margin_bounds (r : LowerCapRectangle bStar) :
    r.margin ≤ (r.left+2)/2 ∧ r.margin ≤ (2-r.right)/2 ∧
    r.margin ≤ (r.bottom+2)/2 ∧ r.margin ≤ (bStar-r.top)/2 := by
  unfold margin
  refine ⟨min_le_left _ _, ?_, ?_, ?_⟩
  · exact (min_le_right _ _).trans (min_le_left _ _)
  · exact ((min_le_right _ _).trans (min_le_right _ _)).trans (min_le_left _ _)
  · exact ((min_le_right _ _).trans (min_le_right _ _)).trans (min_le_right _ _)

def expand (r : LowerCapRectangle bStar) : LowerCapRectangle bStar where
  left := r.left-r.margin
  right := r.right+r.margin
  bottom := r.bottom-r.margin
  top := r.top+r.margin
  left_gt := by linarith [r.margin_bounds.1,r.left_gt]
  right_lt := by linarith [r.margin_bounds.2.1,r.right_lt]
  bottom_gt := by linarith [r.margin_bounds.2.2.1,r.bottom_gt]
  horizontal := by linarith [r.horizontal,r.margin_pos]
  vertical := by linarith [r.vertical,r.margin_pos]
  top_lt := by linarith [r.margin_bounds.2.2.2,r.top_lt]
  ceiling_le := r.ceiling_le

theorem region_subset_expand (r : LowerCapRectangle bStar) : r.region ⊆ r.expand.region := by
  intro p hp
  exact ⟨⟨by change r.left-r.margin ≤ p 0; linarith [hp.1.1,r.margin_pos],
    by change p 0 ≤ r.right+r.margin; linarith [hp.1.2,r.margin_pos]⟩,
    ⟨by change r.bottom-r.margin ≤ p 1; linarith [hp.2.1,r.margin_pos],
      by change p 1 ≤ r.top+r.margin; linarith [hp.2.2,r.margin_pos]⟩⟩

theorem expand_shrink_region (r : LowerCapRectangle bStar) :
    closedRectangle (r.expand.left+r.margin) (r.expand.right-r.margin)
      (r.expand.bottom+r.margin) (r.expand.top-r.margin) = r.region := by
  dsimp only [expand, region]
  congr 1 <;> ring

theorem image_subset_energyOuter (r : LowerCapRectangle bStar) (Y : ℝ → ℝ → ℝ) :
    r.image Y ⊆ r.energyOuter.image Y := Set.image_mono r.region_subset_energyOuter

theorem image_subset_expand (r : LowerCapRectangle bStar) (Y : ℝ → ℝ → ℝ) :
    r.image Y ⊆ r.expand.image Y := Set.image_mono r.region_subset_expand

end LowerCapRectangle

variable {bStar : ℝ}

theorem coordinateL2Bound_to_expanded_cap_coordinateBound
    {q z : Coord → ℝ} {U : Set Coord} {Y : ℝ → ℝ → ℝ}
    (hq : ContDiffOn ℝ ∞ q U) (hU : IsOpen U) (hSU : modelSquare ⊆ U)
    (hY : ContinuousOn (uncurry Y) (Icc (-2 : ℝ) 2 ×ˢ Icc (-2 : ℝ) 2))
    (hrange : ∀ s ∈ Icc (-2 : ℝ) 2, ∀ t ∈ Icc (-2 : ℝ) 2, Y s t ∈ Icc (-3 : ℝ) 3)
    (hstart : ∀ s ∈ Icc (-2 : ℝ) 2, Y s 0 = s)
    (hode : ∀ s ∈ Icc (-2 : ℝ) 2, ∀ t ∈ Icc (-2 : ℝ) 2,
      HasDerivWithinAt (Y s) (-q (coordinatePoint t (Y s t))) (Icc (-2 : ℝ) 2) t)
    {M : ℝ} (hM : 0 ≤ M)
    (hq0 : ∀ p ∈ modelSquare, |q p| ≤ (1 : ℝ)/100)
    (hq1 : ∀ p ∈ modelSquare, |coordPartial 1 q p| ≤ M)
    (hz : ContDiffOn ℝ ∞ z U) (r : LowerCapRectangle bStar) {n : ℕ} {H : ℝ≥0}
    (hL : SmoothLocal.HighEquation.CoordinateL2Bound z (r.expand.image Y) (n+2) H) :
    CoordinateBound z (r.image Y) n
      ((SmoothLocal.Sobolev.squareSobolevWeight (flowInteriorRadius M r.margin r.margin)+1)*(H : ℝ)) := by
  have h := coordinateL2Bound_to_nested_flow_coordinateBound hq hU hSU hY hrange hstart hode
    hM hq0 hq1 r.expand.left_gt r.expand.right_lt r.expand.bottom_gt
    (by linarith [r.expand.top_lt,r.expand.ceiling_le]) r.margin_pos r.margin_pos hz hL
  simpa only [LowerCapRectangle.expand_shrink_region, LowerCapRectangle.image] using h

end SmoothLocal.Flow

end

end OAI
