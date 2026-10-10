import OAI.Combinatorics.Crossing.SegmentCrossingCoordinates

namespace OAI

noncomputable section
namespace Zarankiewicz

theorem properCrossing_openSegments (a b c d x : Plane) (hd : det2 (b-a) (d-c) ≠ 0)
    (hx : x ∈ openSegmentTrace a b) (hy : x ∈ openSegmentTrace c d) :
    ProperCrossing (openSegmentTrace a b) (openSegmentTrace c d) x := by
  obtain ⟨t,ht,hxt⟩ := hx
  obtain ⟨u,hu,hxu⟩ := hy
  let U : Set Plane := Set.Ioo (-t) (1-t) ×ˢ Set.Ioo (-u) (1-u)
  have hU : IsOpen U := isOpen_Ioo.prod isOpen_Ioo
  let chart := crossingCoordinateChart x (b-a) (d-c) hd U hU
  have hzero : (0,0) ∈ U := ⟨⟨by linarith [ht.1],by linarith [ht.2]⟩,
    ⟨by linarith [hu.1],by linarith [hu.2]⟩⟩
  have hsource : x ∈ chart.source := by
    change crossingCoordinates x (b-a) (d-c) x ∈ U
    rw [crossingCoordinates_origin]
    exact hzero
  refine ⟨chart,hsource,crossingCoordinates_origin x (b-a) (d-c),?_,?_⟩
  · apply Set.Subset.antisymm
    · rintro y ⟨z,hz,rfl⟩
      refine ⟨chart.map_source hz.1,?_⟩
      obtain ⟨s,hs,he⟩ := hz.2
      rw [← he]
      change (crossingCoordinates x (b-a) (d-c) (segmentPoint a b s)).2=0
      rw [crossingCoordinates_first_segment a b c d x t s hd hxt.symm]
    · rintro y ⟨hy,hy0⟩
      have hs : t+y.1 ∈ Set.Ioo (0 : ℝ) 1 := ⟨by linarith [hy.1.1],by linarith [hy.1.2]⟩
      have he : chart (segmentPoint a b (t+y.1))=y := by
        change crossingCoordinates x (b-a) (d-c) (segmentPoint a b (t+y.1))=y
        rw [crossingCoordinates_first_segment a b c d x t (t+y.1) hd hxt.symm]
        apply Prod.ext
        · dsimp
          ring
        · exact hy0.symm
      refine ⟨segmentPoint a b (t+y.1),⟨?_,⟨t+y.1,hs,rfl⟩⟩,he⟩
      change chart (segmentPoint a b (t+y.1)) ∈ U
      rw [he]
      exact hy
  · apply Set.Subset.antisymm
    · rintro y ⟨z,hz,rfl⟩
      refine ⟨chart.map_source hz.1,?_⟩
      obtain ⟨s,hs,he⟩ := hz.2
      rw [← he]
      change (crossingCoordinates x (b-a) (d-c) (segmentPoint c d s)).1=0
      rw [crossingCoordinates_second_segment a b c d x u s hd hxu.symm]
    · rintro y ⟨hy,hy0⟩
      have hs : u+y.2 ∈ Set.Ioo (0 : ℝ) 1 := ⟨by linarith [hy.2.1],by linarith [hy.2.2]⟩
      have he : chart (segmentPoint c d (u+y.2))=y := by
        change crossingCoordinates x (b-a) (d-c) (segmentPoint c d (u+y.2))=y
        rw [crossingCoordinates_second_segment a b c d x u (u+y.2) hd hxu.symm]
        apply Prod.ext
        · exact hy0.symm
        · dsimp
          ring
      refine ⟨segmentPoint c d (u+y.2),⟨?_,⟨u+y.2,hs,rfl⟩⟩,he⟩
      change chart (segmentPoint c d (u+y.2)) ∈ U
      rw [he]
      exact hy

end Zarankiewicz

end

end OAI
