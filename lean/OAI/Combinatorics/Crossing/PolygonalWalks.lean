import OAI.Combinatorics.Crossing.SegmentSymmetries
import Mathlib.Analysis.Convex.PathConnected

namespace OAI

noncomputable section
namespace Zarankiewicz
open scoped BigOperators

def polygonalPath (v : ℕ → Plane) : (n : ℕ) → Path (v 0) (v n)
  | 0 => Path.refl (v 0)
  | n+1 => (polygonalPath v n).trans (Path.segment (v n) (v (n+1)))

def polygonIntersection (v w : ℕ → Plane) (n m : ℕ) : ℝ :=
  ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range m,
    segmentCrossingSign (v i) (v (i+1)) (w j) (w (j+1))

theorem polygonIntersection_swap (v w : ℕ → Plane) (n m : ℕ) :
    polygonIntersection w v m n = -polygonIntersection v w n m := by
  unfold polygonIntersection
  rw [Finset.sum_comm]
  calc
    _ = ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range m,
        -segmentCrossingSign (v i) (v (i+1)) (w j) (w (j+1)) := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      exact segmentCrossingSign_swap _ _ _ _
    _ = _ := by simp only [Finset.sum_neg_distrib]

theorem telescoping_real_sum (f : ℕ → ℝ) (n : ℕ) :
    (∑ i ∈ Finset.range n, (f i-f (i+1))) = f 0-f n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ,ih]
    ring

def triangleSegmentIntersection (o a b c d : Plane) : ℝ :=
  segmentCrossingSign o a c d + segmentCrossingSign a b c d + segmentCrossingSign b o c d

theorem polygon_cone_cancellation (v : ℕ → Plane) (n : ℕ) (hv : v n = v 0)
    (o c d : Plane) :
    (∑ i ∈ Finset.range n, triangleSegmentIntersection o (v i) (v (i+1)) c d) =
      ∑ i ∈ Finset.range n, segmentCrossingSign (v i) (v (i+1)) c d := by
  unfold triangleSegmentIntersection
  have hrev : ∀ i, segmentCrossingSign (v (i+1)) o c d = -segmentCrossingSign o (v (i+1)) c d :=
    fun i => segmentCrossingSign_reverse_left o (v (i+1)) c d
  simp only [hrev, Finset.sum_add_distrib]
  have htele := telescoping_real_sum (fun i => segmentCrossingSign o (v i) c d) n
  rw [hv,sub_self] at htele
  rw [Finset.sum_sub_distrib] at htele
  rw [Finset.sum_neg_distrib]
  linarith

end Zarankiewicz

end

end OAI
