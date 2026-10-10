import OAI.Combinatorics.Crossing.TriangleSideEvent
import OAI.Combinatorics.Crossing.SortedSideEvents
import OAI.Combinatorics.Crossing.PolygonalWalks
import Mathlib.Tactic.FinCases

namespace OAI

noncomputable section
namespace Zarankiewicz
open scoped BigOperators Classical

def triangleStart (a b c : Plane) : Fin 3 → Plane := ![a,b,c]
def triangleEnd (a b c : Plane) : Fin 3 → Plane := ![b,c,a]
def triangleIndicator (a b c z : Plane) : ℝ :=
  ∏ i : Fin 3, positiveIndicator (orient2 (triangleStart a b c i) (triangleEnd a b c i) z)

theorem triangle_area_cycle (a b c : Plane) : orient2 b c a = orient2 a b c := by
  dsimp [orient2,det2]
  ring

theorem affine_side_factor (a b c d : Plane) (hn : det2 (b-a) (d-c) ≠ 0) (t : ℝ) :
    orient2 a b (segmentPoint c d t) =
      det2 (b-a) (d-c) * (t-secondIntersectionParameter a b c d) := by
  rw [orient2_segment]
  change (1-t)*orient2 a b c+t*orient2 a b d =
    det2 (b-a) (d-c)*(t-(-orient2 a b c / det2 (b-a) (d-c)))
  field_simp
  linear_combination t * (orient2_difference a b c d)

theorem triangle_segment_entry_exit (a b c d e : Plane)
    (harea : 0 < orient2 a b c)
    (hn : ∀ i : Fin 3, det2 (triangleEnd a b c i-triangleStart a b c i) (e-d) ≠ 0)
    (hr : Function.Injective (fun i : Fin 3 =>
      secondIntersectionParameter (triangleStart a b c i) (triangleEnd a b c i) d e))
    (h0 : ∀ i : Fin 3, secondIntersectionParameter (triangleStart a b c i) (triangleEnd a b c i) d e ≠ 0)
    (h1 : ∀ i : Fin 3, secondIntersectionParameter (triangleStart a b c i) (triangleEnd a b c i) d e ≠ 1) :
    triangleSegmentIntersection a b c d e = triangleIndicator a b c e-triangleIndicator a b c d := by
  let r := fun i : Fin 3 => secondIntersectionParameter (triangleStart a b c i) (triangleEnd a b c i) d e
  let b' := fun i : Fin 3 => det2 (triangleEnd a b c i-triangleStart a b c i) (e-d)
  have hf (i : Fin 3) (t : ℝ) : b' i*(t-r i) =
      orient2 (triangleStart a b c i) (triangleEnd a b c i) (segmentPoint d e t) :=
    (affine_side_factor _ _ d e (hn i) t).symm
  have hc1 : 0 < orient2 b c a := by rwa [triangle_area_cycle]
  have hc2 : 0 < orient2 c a b := by rwa [triangle_area_cycle,triangle_area_cycle]
  have hs (i : Fin 3) :
      segmentCrossingSign (triangleStart a b c i) (triangleEnd a b c i) d e =
        if 0<r i ∧ r i<1 then slopeSign (b' i) *
          (∏ j : Fin 3, if j=i then 1 else positiveIndicator
            (orient2 (triangleStart a b c j) (triangleEnd a b c j) (segmentPoint d e (r i)))) else 0 := by
    fin_cases i
    · simpa [r,b',triangleStart,triangleEnd,Fin.prod_univ_succ] using
        segmentCrossingSign_triangle_event a b c d e harea (hn 0)
    · simpa [r,b',triangleStart,triangleEnd,Fin.prod_univ_succ,mul_comm] using
        segmentCrossingSign_triangle_event b c a d e hc1 (hn 1)
    · simpa [r,b',triangleStart,triangleEnd,Fin.prod_univ_succ] using
        segmentCrossingSign_triangle_event c a b d e hc2 (hn 2)
  have h := sum_affine_side_events_unordered 3 r b' hr hn h0 h1
  simp_rw [hf] at h
  simp only [segmentPoint_one,segmentPoint_zero] at h
  calc
    triangleSegmentIntersection a b c d e =
        ∑ i : Fin 3, segmentCrossingSign (triangleStart a b c i) (triangleEnd a b c i) d e := by
      simp [triangleSegmentIntersection,triangleStart,triangleEnd,Fin.sum_univ_succ]
      ring
    _ = _ := by simpa only [hs,triangleIndicator] using h

end Zarankiewicz

end

end OAI
