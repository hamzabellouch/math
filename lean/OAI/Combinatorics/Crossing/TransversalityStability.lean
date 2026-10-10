import OAI.Combinatorics.Crossing.SegmentContinuity

namespace OAI

noncomputable section
namespace Zarankiewicz
open scoped Topology Classical

theorem segmentPairTransverse_of_proper (a b c d : Plane) (h : SegmentsCrossProperly a b c d) :
    SegmentPairTransverse a b c d := by
  obtain ⟨hn,t₀,ht₀,u₀,hu₀,he₀⟩ := h
  intro t ht u hu he
  obtain ⟨rfl,rfl⟩ := segment_intersection_parameters_unique a b c d hn t u t₀ u₀ he he₀
  exact ⟨hn,ht₀,hu₀⟩

theorem segmentPairTransverse_swap (a b c d : Plane) (h : SegmentPairTransverse a b c d) :
    SegmentPairTransverse c d a b := by
  intro t ht u hu he
  obtain ⟨hn,hu',ht'⟩ := h u hu t ht he.symm
  refine ⟨?_,ht',hu'⟩
  rw [det2_swap]
  exact neg_ne_zero.mpr hn

theorem eventually_segmentPairTransverse (a b c d : Plane) (h : SegmentPairTransverse a b c d) :
    ∀ᶠ ab : Plane × Plane in 𝓝 (a,b), SegmentPairTransverse ab.1 ab.2 c d := by
  by_cases hc : SegmentsCrossProperly a b c d
  · have hsign : segmentCrossingSign a b c d ≠ 0 := by
      unfold segmentCrossingSign
      rw [ite_eq_left hc]
      split_ifs <;> norm_num
    filter_upwards [eventually_segmentCrossingSign_of_proper a b c d hc] with ab hab
    apply segmentPairTransverse_of_proper
    by_contra hn
    have hz : segmentCrossingSign ab.1 ab.2 c d = 0 := by simp [segmentCrossingSign,hn]
    exact hsign (hab.symm.trans hz)
  · have hn : ¬ ClosedSegmentsMeet a b c d := by
      rintro ⟨t,ht,u,hu,he⟩
      obtain ⟨hd,ht',hu'⟩ := h t ht u hu he
      exact hc ⟨hd,t,ht',u,hu',he⟩
    have hevent := (isClosed_closedSegmentsMeet c d).isOpen_compl.mem_nhds
      (show (a,b) ∈ {ab : Plane × Plane | ClosedSegmentsMeet ab.1 ab.2 c d}ᶜ from hn)
    filter_upwards [hevent] with ab hab
    intro t ht u hu he
    exact False.elim (hab ⟨t,ht,u,hu,he⟩)

end Zarankiewicz

end

end OAI
