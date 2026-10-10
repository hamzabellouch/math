import OAI.Probability.InvariantIsing.Haar.PlaneRotation

namespace OAI

/-! The finite matrix contraction behind the orthogonal-group curvature calculation. -/
noncomputable section
open Matrix
open scoped BigOperators
namespace InvariantIsing

lemma planeGenerator_sandwich {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ) (i j : Fin N) :
    planeGenerator i j*A*planeGenerator i j =
      Matrix.single i j (A j i)-Matrix.single j j (A i i)-
        Matrix.single i i (A j j)+Matrix.single j i (A i j) := by
  simp only [planeGenerator,sub_mul,mul_sub,Matrix.single_mul_mul_single,one_mul,mul_one]
  abel

lemma sum_single_transpose {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ) :
    (∑ i, ∑ j, Matrix.single i j (A j i)) = A.transpose := by
  classical
  ext k l
  simp [Matrix.sum_apply,Matrix.single_apply,ite_and]

lemma sum_single_trace_diagonal {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ) :
    (∑ i, ∑ j, Matrix.single i i (A j j)) = A.trace • (1 : Matrix (Fin N) (Fin N) ℝ) := by
  classical
  ext k l
  by_cases h : k=l
  · subst l
    simp [Matrix.sum_apply,Matrix.single_apply,Matrix.trace,Matrix.diag_apply]
  · simp [Matrix.sum_apply,Matrix.single_apply,h,ite_and]

theorem sum_planeGenerator_sandwich {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ) :
    (∑ i, ∑ j, planeGenerator i j*A*planeGenerator i j) =
      (2 : ℝ) • A.transpose-(2*A.trace) • (1 : Matrix (Fin N) (Fin N) ℝ) := by
  simp_rw [planeGenerator_sandwich,Finset.sum_add_distrib,Finset.sum_sub_distrib]
  have hs : (∑ i : Fin N, ∑ j : Fin N, Matrix.single j i (A i j)) = A.transpose := by
    rw [Finset.sum_comm]
    exact sum_single_transpose A
  have hd : (∑ i : Fin N, ∑ j : Fin N, Matrix.single j j (A i i)) =
      A.trace • (1 : Matrix (Fin N) (Fin N) ℝ) := by
    rw [Finset.sum_comm]
    exact sum_single_trace_diagonal A
  rw [sum_single_transpose,sum_single_trace_diagonal,hs,hd]
  module

end InvariantIsing

end

end OAI
