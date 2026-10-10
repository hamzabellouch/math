import OAI.Combinatorics.Crossing.SegmentCrossingCoordinates
import Mathlib.Analysis.Convex.PathConnected

namespace OAI

noncomputable section
namespace Zarankiewicz

theorem crossingCoordinates_affine (o u v a b : Plane) (t : ℝ) :
    crossingCoordinates o u v (segmentPoint a b t)=
      segmentPoint (crossingCoordinates o u v a) (crossingCoordinates o u v b) t := by
  apply Prod.ext <;> dsimp [crossingCoordinates,segmentPoint,det2] <;>
    simp only [div_eq_mul_inv] <;> ring

theorem convex_combination_pos (a b t : ℝ) (ha : 0 < a) (hb : 0 < b)
    (ht : t ∈ Set.Icc (0 : ℝ) 1) : 0 < (1-t)*a+t*b := by
  have hm : 0 < min a b := lt_min ha hb
  have hl := mul_le_mul_of_nonneg_left (min_le_left a b) (sub_nonneg.mpr ht.2)
  have hr := mul_le_mul_of_nonneg_left (min_le_right a b) ht.1
  nlinarith

theorem crossing_reconnections_disjoint (a b c d : Plane) (h : SegmentsCrossProperly a b c d) :
    Disjoint (segment ℝ c b) (segment ℝ a d) := by
  obtain ⟨hd,s,hs,t,ht,hst⟩ := h
  let o := segmentPoint a b s
  let F := crossingCoordinates o (b-a) (d-c)
  have hFa : F a=(-s,0) := by
    have he := crossingCoordinates_first_segment a b c d o s 0 hd rfl
    simpa only [segmentPoint_zero,zero_sub] using he
  have hFb : F b=(1-s,0) := by
    have he := crossingCoordinates_first_segment a b c d o s 1 hd rfl
    simpa only [segmentPoint_one] using he
  have hFc : F c=(0,-t) := by
    have he := crossingCoordinates_second_segment a b c d o t 0 hd hst
    simpa only [segmentPoint_zero,zero_sub] using he
  have hFd : F d=(0,1-t) := by
    have he := crossingCoordinates_second_segment a b c d o t 1 hd hst
    simpa only [segmentPoint_one] using he
  apply Set.disjoint_left.mpr
  intro x hleft hright
  rw [← Path.range_segment] at hleft hright
  obtain ⟨u,hu⟩ := hleft
  obtain ⟨v,hv⟩ := hright
  have hu' : segmentPoint c b u.val=x := by
    simpa only [Path.segment_apply,AffineMap.lineMap_apply_module,segmentPoint] using hu
  have hv' : segmentPoint a d v.val=x := by
    simpa only [Path.segment_apply,AffineMap.lineMap_apply_module,segmentPoint] using hv
  have hleftF : F x=segmentPoint (0,-t) (1-s,0) u.val := by
    rw [← hu']
    exact (crossingCoordinates_affine o (b-a) (d-c) c b u.val).trans (by
      change segmentPoint (F c) (F b) u.val=_
      rw [hFc,hFb])
  have hrightF : F x=segmentPoint (-s,0) (0,1-t) v.val := by
    rw [← hv']
    exact (crossingCoordinates_affine o (b-a) (d-c) a d v.val).trans (by
      change segmentPoint (F a) (F d) v.val=_
      rw [hFa,hFd])
  have hl : 0 < (F x).1-(F x).2 := by
    rw [hleftF]
    have hh := convex_combination_pos t (1-s) u.val ht.1 (sub_pos.mpr hs.2) u.property
    dsimp [segmentPoint]
    nlinarith
  have hr : (F x).1-(F x).2 < 0 := by
    rw [hrightF]
    have hh := convex_combination_pos s (1-t) v.val hs.1 (sub_pos.mpr ht.2) v.property
    dsimp [segmentPoint]
    nlinarith
  exact hl.not_ge hr.le

end Zarankiewicz

end

end OAI
