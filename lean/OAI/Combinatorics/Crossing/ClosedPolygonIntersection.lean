import OAI.Combinatorics.Crossing.TransversePolygonIntersection
import OAI.Combinatorics.Crossing.PolygonTransversalityStability

namespace OAI

noncomputable section
namespace Zarankiewicz

theorem closed_polygon_intersection_zero (v w : ℕ → Plane) (n m : ℕ)
    (hc : v n=v 0) (hd : w m=w 0)
    (ht : ∀ i : Fin n, ∀ j : Fin m,
      SegmentPairTransverse (v i.val) (v (i.val+1)) (w j.val) (w (j.val+1))) :
    polygonIntersection v w n m = 0 := by
  by_cases hm : 1<m
  · have hm0 : 0<m := by omega
    have hswap (j : Fin m) (i : Fin n) :
        SegmentPairTransverse (w j.val) (w (j.val+1)) (v i.val) (v (i.val+1)) :=
      segmentPairTransverse_swap _ _ _ _ (ht i j)
    obtain ⟨ε,hε,hstable⟩ := exists_polygon_transversality_radius w v m n hswap
    obtain ⟨p,hnear,hinj,_⟩ := exists_generic_point_family
      (fun i : Fin 0 => (Fin.elim0 i : Plane)) (fun i : Fin 0 => (Fin.elim0 i : Plane))
      (fun i : Fin 0 => (Fin.elim0 i : Plane)) (fun i => Fin.elim0 i)
      m (fun i => w i.val) (fun _ => ε) (fun _ => hε)
    let w' := periodicPolygon m hm0 p
    have hclose : w' m=w' 0 := periodicPolygon_closed m hm0 p
    have hw' (j : Fin m) : w' (j.val+1) ≠ w' j.val := hinj.ne (cyclicIndex_succ_ne m hm j)
    obtain ⟨htrans,heq⟩ := hstable w' (periodicPolygon_near m hm0 w hd p ε hnear)
    have hzero := polygon_intersection_zero_transverse v w' n m hc hclose hw'
      (fun i j => segmentPairTransverse_swap _ _ _ _ (htrans j i))
    have hrev := polygonIntersection_swap v w' n m
    rw [hzero,neg_zero,heq] at hrev
    rw [polygonIntersection_swap v w n m] at hrev
    exact neg_eq_zero.mp hrev
  · have hm' : m=0 ∨ m=1 := by omega
    rcases hm' with rfl | rfl
    · simp [polygonIntersection]
    · have hz : polygonIntersection w v 1 n = 0 := by
        simp only [polygonIntersection,Finset.sum_range_one]
        rw [hd]
        simp only [segmentCrossingSign_self_left,Finset.sum_const_zero]
      rw [polygonIntersection_swap v w n 1] at hz
      exact neg_eq_zero.mp hz

end Zarankiewicz

end

end OAI
