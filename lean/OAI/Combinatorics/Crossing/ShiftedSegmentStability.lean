import OAI.Combinatorics.Crossing.TransversalityStability
import OAI.Combinatorics.Crossing.FiniteEventualRadius

namespace OAI

noncomputable section
namespace Zarankiewicz
open scoped Topology

theorem shifted_endpoints_tendsto (c d qc qd : Plane) :
    Filter.Tendsto (fun t : ℝ => (c+t • qc,d+t • qd)) (𝓝 0) (𝓝 (c,d)) := by
  have hh : Continuous (fun t : ℝ => (c+t • qc,d+t • qd)) := by fun_prop
  simpa [ContinuousAt] using hh.continuousAt (x := 0)

theorem eventually_shifted_segment_pair (a b c d qc qd : Plane)
    (h : SegmentPairTransverse a b c d) :
    ∀ᶠ t : ℝ in 𝓝 0,
      SegmentPairTransverse a b (c+t • qc) (d+t • qd) ∧
      segmentCrossingSign a b (c+t • qc) (d+t • qd)=segmentCrossingSign a b c d := by
  have hs := segmentPairTransverse_swap a b c d h
  have he := (shifted_endpoints_tendsto c d qc qd).eventually
    ((eventually_segmentPairTransverse c d a b hs).and (eventually_segmentCrossingSign c d a b hs))
  filter_upwards [he] with t ht
  refine ⟨segmentPairTransverse_swap _ _ _ _ ht.1,?_⟩
  have hsign := ht.2
  rw [segmentCrossingSign_swap a b _ _,segmentCrossingSign_swap a b c d] at hsign
  exact neg_injective hsign

theorem closedSegmentsMeet_symm (a b c d : Plane) : ClosedSegmentsMeet a b c d ↔ ClosedSegmentsMeet c d a b := by
  constructor <;> rintro ⟨t,ht,u,hu,he⟩ <;> exact ⟨u,hu,t,ht,he.symm⟩

theorem eventually_shifted_disjoint_segments (a b c d qc qd : Plane)
    (h : ¬ ClosedSegmentsMeet a b c d) :
    ∀ᶠ t : ℝ in 𝓝 0, ¬ ClosedSegmentsMeet a b (c+t • qc) (d+t • qd) := by
  have hn : (c,d) ∈ {ab : Plane × Plane | ClosedSegmentsMeet ab.1 ab.2 a b}ᶜ := by
    intro hx
    exact h ((closedSegmentsMeet_symm c d a b).mp hx)
  have he := (shifted_endpoints_tendsto c d qc qd).eventually
    ((isClosed_closedSegmentsMeet a b).isOpen_compl.mem_nhds hn)
  filter_upwards [he] with t ht
  intro hx
  exact ht ((closedSegmentsMeet_symm a b _ _).mp hx)

theorem exists_shifted_segment_pairs_radius {ι : Type*} [Fintype ι]
    (a b c d qc qd : ι → Plane) (h : ∀ i, SegmentPairTransverse (a i) (b i) (c i) (d i)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, |t| < δ → ∀ i,
      SegmentPairTransverse (a i) (b i) (c i+t • qc i) (d i+t • qd i) ∧
      segmentCrossingSign (a i) (b i) (c i+t • qc i) (d i+t • qd i)=
        segmentCrossingSign (a i) (b i) (c i) (d i) := by
  exact finite_eventual_radius _ (fun i => eventually_shifted_segment_pair _ _ _ _ _ _ (h i))

end Zarankiewicz

end

end OAI
