import OAI.Combinatorics.Crossing.ShiftedSegmentStability

namespace OAI

noncomputable section
namespace Zarankiewicz
open scoped Topology

theorem moving_endpoints_tendsto (C D : ℝ → Plane) (c d : Plane)
    (hC : ContinuousAt C 0) (hD : ContinuousAt D 0) (hC0 : C 0=c) (hD0 : D 0=d) :
    Filter.Tendsto (fun t : ℝ => (C t,D t)) (𝓝 0) (𝓝 (c,d)) := by
  simpa [ContinuousAt,hC0,hD0] using hC.prodMk hD

theorem eventually_moving_segment_pair (a b c d : Plane) (C D : ℝ → Plane)
    (hC : ContinuousAt C 0) (hD : ContinuousAt D 0) (hC0 : C 0=c) (hD0 : D 0=d)
    (h : SegmentPairTransverse a b c d) :
    ∀ᶠ t : ℝ in 𝓝 0,
      SegmentPairTransverse a b (C t) (D t) ∧
      segmentCrossingSign a b (C t) (D t)=segmentCrossingSign a b c d := by
  have hs := segmentPairTransverse_swap a b c d h
  have he := (moving_endpoints_tendsto C D c d hC hD hC0 hD0).eventually
    ((eventually_segmentPairTransverse c d a b hs).and (eventually_segmentCrossingSign c d a b hs))
  filter_upwards [he] with t ht
  refine ⟨segmentPairTransverse_swap _ _ _ _ ht.1,?_⟩
  have hsign := ht.2
  rw [segmentCrossingSign_swap a b _ _,segmentCrossingSign_swap a b c d] at hsign
  exact neg_injective hsign

theorem eventually_moving_disjoint_segments (a b c d : Plane) (C D : ℝ → Plane)
    (hC : ContinuousAt C 0) (hD : ContinuousAt D 0) (hC0 : C 0=c) (hD0 : D 0=d)
    (h : ¬ ClosedSegmentsMeet a b c d) :
    ∀ᶠ t : ℝ in 𝓝 0, ¬ ClosedSegmentsMeet a b (C t) (D t) := by
  have hn : (c,d) ∈ {ab : Plane × Plane | ClosedSegmentsMeet ab.1 ab.2 a b}ᶜ := by
    intro hx
    exact h ((closedSegmentsMeet_symm c d a b).mp hx)
  have he := (moving_endpoints_tendsto C D c d hC hD hC0 hD0).eventually
    ((isClosed_closedSegmentsMeet a b).isOpen_compl.mem_nhds hn)
  filter_upwards [he] with t ht
  intro hx
  exact ht ((closedSegmentsMeet_symm a b _ _).mp hx)

end Zarankiewicz

end

end OAI
