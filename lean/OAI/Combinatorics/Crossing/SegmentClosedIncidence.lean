import OAI.Combinatorics.Crossing.SegmentContinuity
import Mathlib.Analysis.Convex.PathConnected

namespace OAI

noncomputable section
namespace Zarankiewicz

theorem closedSegmentsMeet_iff_nonempty_inter (a b c d : Plane) :
    ClosedSegmentsMeet a b c d ↔ (segment ℝ a b ∩ segment ℝ c d).Nonempty := by
  constructor
  · rintro ⟨s,hs,t,ht,he⟩
    refine ⟨segmentPoint a b s,?_,?_⟩
    · rw [← Path.range_segment]
      exact ⟨⟨s,hs⟩,by simp only [Path.segment_apply,AffineMap.lineMap_apply_module,segmentPoint]⟩
    · rw [← Path.range_segment]
      exact ⟨⟨t,ht⟩,by simpa only [Path.segment_apply,AffineMap.lineMap_apply_module,segmentPoint] using he.symm⟩
  · rintro ⟨x,hx,hy⟩
    rw [← Path.range_segment] at hx hy
    obtain ⟨s,hs⟩ := hx
    obtain ⟨t,ht⟩ := hy
    refine ⟨s.val,s.property,t.val,t.property,?_⟩
    simpa only [Path.segment_apply,AffineMap.lineMap_apply_module,segmentPoint] using hs.trans ht.symm

theorem not_closedSegmentsMeet_of_disjoint (a b c d : Plane)
    (h : Disjoint (segment ℝ a b) (segment ℝ c d)) : ¬ ClosedSegmentsMeet a b c d := by
  intro hh
  obtain ⟨x,hx,hy⟩ := (closedSegmentsMeet_iff_nonempty_inter a b c d).mp hh
  exact Set.disjoint_left.mp h hx hy

end Zarankiewicz

end

end OAI
