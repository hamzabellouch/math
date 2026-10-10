import OAI.Combinatorics.Crossing.PathConcatenationInjective
import OAI.Combinatorics.Crossing.PlanarSegments

namespace OAI

noncomputable section
namespace Zarankiewicz

theorem openSegmentTrace_subset_segment (a b : Plane) : openSegmentTrace a b ⊆ segment ℝ a b := by
  rintro x ⟨t,ht,he⟩
  rw [← Path.range_segment]
  exact ⟨⟨t,⟨ht.1.le,ht.2.le⟩⟩,by simpa only [Path.segment_apply,AffineMap.lineMap_apply_module,segmentPoint] using he⟩

theorem openSegmentTrace_ne_endpoints (a b : Plane) (hab : a ≠ b)
    (x : Plane) (hx : x ∈ openSegmentTrace a b) : x ≠ a ∧ x ≠ b := by
  obtain ⟨t,ht,he⟩ := hx
  let u : unitInterval := ⟨t,⟨ht.1.le,ht.2.le⟩⟩
  have hu : (Path.segment a b) u=x := by
    simpa only [Path.segment_apply,AffineMap.lineMap_apply_module,segmentPoint] using he
  constructor
  · intro h
    have hh := Path.segment_injective_of_ne hab (hu.trans (h.trans (Path.segment a b).source.symm))
    have ht0 : t=0 := congrArg Subtype.val hh
    exact ht.1.ne ht0.symm
  · intro h
    have hh := Path.segment_injective_of_ne hab (hu.trans (h.trans (Path.segment a b).target.symm))
    have ht1 : t=1 := congrArg Subtype.val hh
    exact ht.2.ne ht1

end Zarankiewicz

end

end OAI
