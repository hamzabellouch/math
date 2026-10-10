import OAI.Combinatorics.Crossing.SegmentContinuity
import OAI.Combinatorics.Crossing.PolygonalWalks
import OAI.Combinatorics.Crossing.FiniteSeparation

namespace OAI

noncomputable section
namespace Zarankiewicz
open scoped Classical BigOperators

theorem exists_polygon_intersection_stability_radius (v w : ℕ → Plane) (n m : ℕ)
    (h : ∀ i : Fin n, ∀ j : Fin m,
      SegmentPairTransverse (v i.val) (v (i.val+1)) (w j.val) (w (j.val+1))) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ v' : ℕ → Plane,
      (∀ i : Fin (n+1), dist (v' i.val) (v i.val) < ε) →
      polygonIntersection v' w n m = polygonIntersection v w n m := by
  have hh : ∀ ij : Fin n × Fin m, ∃ ε : ℝ, 0 < ε ∧
      ∀ ab : Plane × Plane, dist ab (v ij.1.val,v (ij.1.val+1)) < ε →
        segmentCrossingSign ab.1 ab.2 (w ij.2.val) (w (ij.2.val+1)) =
          segmentCrossingSign (v ij.1.val) (v (ij.1.val+1)) (w ij.2.val) (w (ij.2.val+1)) := by
    intro ij
    obtain ⟨ε,hε,he⟩ := Metric.eventually_nhds_iff.mp
      (eventually_segmentCrossingSign _ _ _ _ (h ij.1 ij.2))
    exact ⟨ε,hε,fun ab hab => he hab⟩
  choose radius hpos hstable using hh
  obtain ⟨ε,hε,hbound⟩ := finite_positive_lower_bound Finset.univ radius (fun ij _ => hpos ij)
  refine ⟨ε,hε,?_⟩
  intro v' hv'
  unfold polygonIntersection
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  have hin := Finset.mem_range.mp hi
  have hjm := Finset.mem_range.mp hj
  let ii : Fin n := ⟨i,hin⟩
  let jj : Fin m := ⟨j,hjm⟩
  apply hstable (ii,jj) (v' i,v' (i+1))
  rw [Prod.dist_eq]
  exact (max_lt (hv' ⟨i,by omega⟩) (hv' ⟨i+1,by omega⟩)).trans (hbound (ii,jj) (Finset.mem_univ _))

end Zarankiewicz

end

end OAI
