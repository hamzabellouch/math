import OAI.Combinatorics.Crossing.GenericPolygonIntersection
import OAI.Combinatorics.Crossing.GenericPointFamily
import OAI.Combinatorics.Crossing.PolygonStability
import OAI.Combinatorics.Crossing.PeriodicPolygon

namespace OAI

noncomputable section
namespace Zarankiewicz

theorem segmentCrossingSign_self_left (a c d : Plane) : segmentCrossingSign a a c d = 0 := by
  simp [segmentCrossingSign,SegmentsCrossProperly,det2]

theorem polygon_intersection_zero_transverse (v w : ℕ → Plane) (n m : ℕ)
    (hc : v n=v 0) (hd : w m=w 0)
    (hw : ∀ j : Fin m, w (j.val+1) ≠ w j.val)
    (ht : ∀ i : Fin n, ∀ j : Fin m,
      SegmentPairTransverse (v i.val) (v (i.val+1)) (w j.val) (w (j.val+1))) :
    polygonIntersection v w n m = 0 := by
  by_cases hn : 1<n
  · have hn0 : 0<n := by omega
    obtain ⟨ε,hε,hstable⟩ := exists_polygon_intersection_stability_radius v w n m ht
    obtain ⟨p,hnear,hinj,hpq,hline,hpar,hcorn⟩ := exists_generic_point_family
      (fun j : Fin (m+1) => w j.val) (fun j : Fin m => w j.val)
      (fun j : Fin m => w (j.val+1)-w j.val) (fun j => sub_ne_zero.mpr (hw j))
      n (fun i => v i.val) (fun _ => ε) (fun _ => hε)
    let v' := periodicPolygon n hn0 p
    have hclose : v' n=v' 0 := periodicPolygon_closed n hn0 p
    have hv' (i : Fin n) : v' (i.val+1) ≠ v' i.val :=
      hinj.ne (cyclicIndex_succ_ne n hn i)
    have hpoint (i : Fin (n+1)) (j : Fin (m+1)) : w j.val ≠ v' i.val := hpq _ j
    have hposition : PolygonLinePosition v' w n m := by
      refine ⟨?_,?_,?_⟩
      · intro i j
        exact hpar _ _ (Ne.symm (cyclicIndex_succ_ne n hn i)) j
      · intro i j
        change det2 (w (j.val+1)-w j.val) (p (cyclicIndex n hn0 i.val)-w j.val) ≠ 0
        rw [det2_swap]
        exact neg_ne_zero.mpr (hline _ j)
      · intro i j
        exact hcorn _ _ (Ne.symm (cyclicIndex_succ_ne n hn i)) j
    have hzero := polygon_intersection_zero_in_line_position v' w n m hclose hd hv' hw hpoint hposition
    have heq := hstable v' (periodicPolygon_near n hn0 v hc p ε hnear)
    rwa [heq] at hzero
  · have hn' : n=0 ∨ n=1 := by omega
    rcases hn' with rfl | rfl
    · simp [polygonIntersection]
    · simp only [polygonIntersection,Finset.sum_range_one]
      rw [hc]
      simp only [segmentCrossingSign_self_left,Finset.sum_const_zero]

end Zarankiewicz

end

end OAI
