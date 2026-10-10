import OAI.Combinatorics.Crossing.SegmentContinuity
import Mathlib.Analysis.Convex.PathConnected

namespace OAI

noncomputable section
namespace Zarankiewicz

theorem transverse_segment_intersection_subsingleton (a b c d : Plane)
    (h : SegmentPairTransverse a b c d) :
    (Set.range (Path.segment a b) ∩ Set.range (Path.segment c d)).Subsingleton := by
  intro x hx y hy
  obtain ⟨⟨s,hs⟩,⟨t,ht⟩⟩ := hx
  obtain ⟨⟨u,hu⟩,⟨v,hv⟩⟩ := hy
  have hxs : segmentPoint a b s.val=x := by simpa [Path.segment_apply,AffineMap.lineMap_apply_module,segmentPoint] using hs
  have hxt : segmentPoint c d t.val=x := by simpa [Path.segment_apply,AffineMap.lineMap_apply_module,segmentPoint] using ht
  have hyu : segmentPoint a b u.val=y := by simpa [Path.segment_apply,AffineMap.lineMap_apply_module,segmentPoint] using hu
  have hyv : segmentPoint c d v.val=y := by simpa [Path.segment_apply,AffineMap.lineMap_apply_module,segmentPoint] using hv
  have hdet := (h s.val s.property t.val t.property (hxs.trans hxt.symm)).1
  have he := segment_intersection_parameters_unique a b c d hdet s.val t.val u.val v.val
    (hxs.trans hxt.symm) (hyu.trans hyv.symm)
  exact hxs.symm.trans ((congrArg (segmentPoint a b) he.1).trans hyu)

end Zarankiewicz

end

end OAI
