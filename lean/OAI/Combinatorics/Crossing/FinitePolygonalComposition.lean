import OAI.Combinatorics.Crossing.SegmentTraversalReversal

namespace OAI

noncomputable section
namespace Zarankiewicz
open scoped BigOperators

def finitePolygonalChain (O : Set Plane) (v : ℕ → Plane) (h0 : v 0 ∈ O)
    (P : ∀ i, PolygonalChain O (v i) (v (i+1))) : (n : ℕ) → PolygonalChain O (v 0) (v n)
  | 0 => PolygonalChain.point O (v 0) h0
  | n+1 => (finitePolygonalChain O v h0 P n).join (P n)

theorem finitePolygonalChain_intersection_left (O : Set Plane) (v : ℕ → Plane) (h0 : v 0 ∈ O)
    (P : ∀ i, PolygonalChain O (v i) (v (i+1))) (w : ℕ → Plane) (k n : ℕ) :
    polygonIntersection (finitePolygonalChain O v h0 P n).vertices w (finitePolygonalChain O v h0 P n).pieces k=
      ∑ i ∈ Finset.range n, polygonIntersection (P i).vertices w (P i).pieces k := by
  induction n with
  | zero => simp [finitePolygonalChain,PolygonalChain.point,polygonIntersection]
  | succ n ih =>
    change polygonIntersection ((finitePolygonalChain O v h0 P n).join (P n)).vertices w
      ((finitePolygonalChain O v h0 P n).join (P n)).pieces k=_
    rw [PolygonalChain.intersection_join_left,ih,Finset.sum_range_succ]

theorem finitePolygonalChain_intersection_right (O : Set Plane) (v : ℕ → Plane) (h0 : v 0 ∈ O)
    (P : ∀ i, PolygonalChain O (v i) (v (i+1))) (w : ℕ → Plane) (k n : ℕ) :
    polygonIntersection w (finitePolygonalChain O v h0 P n).vertices k (finitePolygonalChain O v h0 P n).pieces=
      ∑ i ∈ Finset.range n, polygonIntersection w (P i).vertices k (P i).pieces := by
  rw [polygonIntersection_swap,finitePolygonalChain_intersection_left]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  exact (polygonIntersection_swap _ _ _ _).symm

theorem finitePolygonalChain_transverse_left {O T : Set Plane} (v : ℕ → Plane) (h0 : v 0 ∈ O)
    (P : ∀ i, PolygonalChain O (v i) (v (i+1))) {a b : Plane} (Q : PolygonalChain T a b)
    (n : ℕ) (h : ∀ i, i<n → (P i).Transverse Q) : (finitePolygonalChain O v h0 P n).Transverse Q := by
  induction n with
  | zero => intro i; exact Fin.elim0 i
  | succ n ih =>
    exact (finitePolygonalChain O v h0 P n).transverse_join_left (P n) Q
      (ih (fun i hi => h i (by omega))) (h n (by omega))

theorem finitePolygonalChain_transverse_right {O T : Set Plane} (v : ℕ → Plane) (h0 : v 0 ∈ O)
    (P : ∀ i, PolygonalChain O (v i) (v (i+1))) {a b : Plane} (Q : PolygonalChain T a b)
    (n : ℕ) (h : ∀ i, i<n → Q.Transverse (P i)) : Q.Transverse (finitePolygonalChain O v h0 P n) :=
  (finitePolygonalChain O v h0 P n).transverse_swap Q
    (finitePolygonalChain_transverse_left v h0 P Q n (fun i hi => Q.transverse_swap (P i) (h i hi)))

theorem finitePolygonalChain_intersection_double {O T : Set Plane}
    (v w : ℕ → Plane) (hv : v 0 ∈ O) (hw : w 0 ∈ T)
    (P : ∀ i, PolygonalChain O (v i) (v (i+1))) (Q : ∀ j, PolygonalChain T (w j) (w (j+1)))
    (n k : ℕ) :
    polygonIntersection (finitePolygonalChain O v hv P n).vertices (finitePolygonalChain T w hw Q k).vertices
      (finitePolygonalChain O v hv P n).pieces (finitePolygonalChain T w hw Q k).pieces =
      ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range k, polygonIntersection (P i).vertices (Q j).vertices (P i).pieces (Q j).pieces := by
  rw [finitePolygonalChain_intersection_left]
  apply Finset.sum_congr rfl
  intro i hi
  exact finitePolygonalChain_intersection_right _ _ _ _ _ _ _

end Zarankiewicz

end

end OAI
