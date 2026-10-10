import OAI.Combinatorics.Crossing.TransversalityStability
import OAI.Combinatorics.Crossing.PolygonStability

namespace OAI

noncomputable section
namespace Zarankiewicz
open scoped Classical

theorem exists_polygon_transversality_radius (v w : ℕ → Plane) (n m : ℕ)
    (h : ∀ i : Fin n, ∀ j : Fin m,
      SegmentPairTransverse (v i.val) (v (i.val+1)) (w j.val) (w (j.val+1))) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ v' : ℕ → Plane,
      (∀ i : Fin (n+1), dist (v' i.val) (v i.val) < ε) →
      (∀ i : Fin n, ∀ j : Fin m,
        SegmentPairTransverse (v' i.val) (v' (i.val+1)) (w j.val) (w (j.val+1))) ∧
      polygonIntersection v' w n m = polygonIntersection v w n m := by
  have hh : ∀ ij : Fin n × Fin m, ∃ ε : ℝ, 0 < ε ∧
      ∀ ab : Plane × Plane, dist ab (v ij.1.val,v (ij.1.val+1)) < ε →
        SegmentPairTransverse ab.1 ab.2 (w ij.2.val) (w (ij.2.val+1)) := by
    intro ij
    obtain ⟨ε,hε,he⟩ := Metric.eventually_nhds_iff.mp
      (eventually_segmentPairTransverse _ _ _ _ (h ij.1 ij.2))
    exact ⟨ε,hε,fun ab hab => he hab⟩
  choose radius hpos hstable using hh
  obtain ⟨δ,hδ,hbound⟩ := finite_positive_lower_bound Finset.univ radius (fun ij _ => hpos ij)
  obtain ⟨η,hη,hcount⟩ := exists_polygon_intersection_stability_radius v w n m h
  refine ⟨min δ η,lt_min hδ hη,?_⟩
  intro v' hv'
  constructor
  · intro i j
    apply hstable (i,j) (v' i.val,v' (i.val+1))
    rw [Prod.dist_eq]
    have h₀ := (hv' ⟨i.val,by omega⟩).trans_le (min_le_left δ η)
    have h₁ := (hv' ⟨i.val+1,by omega⟩).trans_le (min_le_left δ η)
    exact (max_lt h₀ h₁).trans (hbound (i,j) (Finset.mem_univ _))
  · exact hcount v' (fun i => (hv' i).trans_le (min_le_right δ η))

end Zarankiewicz

end

end OAI
