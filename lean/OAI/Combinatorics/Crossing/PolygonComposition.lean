import OAI.Combinatorics.Crossing.PolygonalWalks
import Mathlib.Algebra.BigOperators.Intervals

namespace OAI

noncomputable section
namespace Zarankiewicz
open scoped BigOperators

def joinedSequence (v w : ℕ → Plane) (n : ℕ) (i : ℕ) : Plane :=
  if i<n then v i else w (i-n)

theorem joinedSequence_left (v w : ℕ → Plane) (n : ℕ) (h : v n=w 0)
    (i : ℕ) (hi : i≤n) : joinedSequence v w n i=v i := by
  unfold joinedSequence
  by_cases hin : i<n
  · rw [ite_eq_left hin]
  · have he : i=n := by omega
    subst i
    simp [h]

theorem joinedSequence_right (v w : ℕ → Plane) (n j : ℕ) :
    joinedSequence v w n (n+j)=w j := by
  simp [joinedSequence,show ¬ n+j<n by omega]

theorem polygonIntersection_join_left (v w z : ℕ → Plane) (n m k : ℕ) (h : v n=w 0) :
    polygonIntersection (joinedSequence v w n) z (n+m) k =
      polygonIntersection v z n k+polygonIntersection w z m k := by
  unfold polygonIntersection
  rw [Finset.sum_range_add]
  congr 1
  · apply Finset.sum_congr rfl
    intro i hi
    have hin := Finset.mem_range.mp hi
    rw [joinedSequence_left v w n h i (by omega),joinedSequence_left v w n h (i+1) (by omega)]
  · apply Finset.sum_congr rfl
    intro i hi
    rw [joinedSequence_right,show n+i+1=n+(i+1) by omega,joinedSequence_right]

theorem polygonIntersection_join_right (v w z : ℕ → Plane) (n m k : ℕ) (h : w m=z 0) :
    polygonIntersection v (joinedSequence w z m) n (m+k) =
      polygonIntersection v w n m+polygonIntersection v z n k := by
  have hh := polygonIntersection_join_left w z v m k n h
  rw [polygonIntersection_swap v (joinedSequence w z m) n (m+k),
    polygonIntersection_swap v w n m,polygonIntersection_swap v z n k] at hh
  linarith

def reversedSequence (v : ℕ → Plane) (n i : ℕ) : Plane := v (n-i)

theorem polygonIntersection_reverse_left (v w : ℕ → Plane) (n m : ℕ) :
    polygonIntersection (reversedSequence v n) w n m = -polygonIntersection v w n m := by
  unfold polygonIntersection
  have he : (∑ i ∈ Finset.range n, ∑ j ∈ Finset.range m,
      segmentCrossingSign (v (n-1-i)) (v (n-1-i+1)) (w j) (w (j+1))) =
      ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range m,
        segmentCrossingSign (v i) (v (i+1)) (w j) (w (j+1)) :=
    Finset.sum_range_reflect (fun i => ∑ j ∈ Finset.range m,
      segmentCrossingSign (v i) (v (i+1)) (w j) (w (j+1))) n
  rw [← he,← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  have hin := Finset.mem_range.mp hi
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  have h₀ : n-i=n-1-i+1 := by omega
  have h₁ : n-(i+1)=n-1-i := by omega
  simp only [reversedSequence,h₀,h₁]
  exact segmentCrossingSign_reverse_left _ _ _ _

end Zarankiewicz

end

end OAI
