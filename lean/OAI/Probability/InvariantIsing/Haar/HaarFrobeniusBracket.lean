import OAI.Probability.InvariantIsing.Haar.HaarPlaneCasimir

namespace OAI

/-! The exact Frobenius bracket contraction for the special orthogonal algebra. -/
noncomputable section
open Matrix
open scoped BigOperators
namespace InvariantIsing

/-- The real, unnormalized Frobenius bilinear form. -/
def matrixFrobeniusPair {N : ℕ} (A B : Matrix (Fin N) (Fin N) ℝ) : ℝ :=
  (A.transpose * B).trace

lemma matrixFrobeniusPair_self {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ) :
    matrixFrobeniusPair A A = ∑ i, ∑ j, (A i j)^2 := by
  simp only [matrixFrobeniusPair,Matrix.trace,Matrix.diag_apply,Matrix.mul_apply,
    Matrix.transpose_apply,pow_two]
  exact Finset.sum_comm

lemma matrixFrobeniusPair_self_nonneg {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ) :
    0 ≤ matrixFrobeniusPair A A := by
  rw [matrixFrobeniusPair_self]
  exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _

lemma planeGenerator_transpose {N : ℕ} (i j : Fin N) :
    (planeGenerator i j).transpose = -planeGenerator i j := by
  simp [planeGenerator,Matrix.transpose_sub,Matrix.transpose_single,neg_sub]

lemma matrixFrobeniusPair_bracket {N : ℕ}
    (E A B : Matrix (Fin N) (Fin N) ℝ) (hE : E.transpose = -E) :
    matrixFrobeniusPair (E*A-A*E) B = -matrixFrobeniusPair A (E*B-B*E) := by
  simp only [matrixFrobeniusPair,Matrix.transpose_sub,Matrix.transpose_mul,hE,
    Matrix.mul_neg,Matrix.neg_mul,Matrix.sub_mul,Matrix.mul_sub,Matrix.trace_sub,
    Matrix.trace_neg]
  rw [← mul_assoc A.transpose E B,Matrix.trace_mul_cycle E A.transpose B]
  rw [Matrix.trace_mul_cycle B E A.transpose]
  simp only [mul_assoc]
  ring

/-- Ordered coordinate planes count each orthogonal tangent direction twice. -/
theorem sum_planeGenerator_bracket_norm_sq {N : ℕ}
    (A : Matrix (Fin N) (Fin N) ℝ) (hA : A.transpose = -A) :
    (∑ i : Fin N, ∑ j : Fin N,
      matrixFrobeniusPair (planeGenerator i j*A-A*planeGenerator i j)
        (planeGenerator i j*A-A*planeGenerator i j)) =
      (4*((N : ℝ)-2))*matrixFrobeniusPair A A := by
  simp_rw [matrixFrobeniusPair_bracket _ _ _ (planeGenerator_transpose _ _)]
  simp only [Finset.sum_neg_distrib]
  have hs : (∑ i : Fin N, ∑ j : Fin N,
      matrixFrobeniusPair A
        (planeGenerator i j*(planeGenerator i j*A-A*planeGenerator i j)-
          (planeGenerator i j*A-A*planeGenerator i j)*planeGenerator i j)) =
      matrixFrobeniusPair A (∑ i : Fin N, ∑ j : Fin N,
        (planeGenerator i j*(planeGenerator i j*A-A*planeGenerator i j)-
          (planeGenerator i j*A-A*planeGenerator i j)*planeGenerator i j)) := by
    simp only [matrixFrobeniusPair,Matrix.mul_sum,Matrix.trace_sum]
  rw [hs,sum_planeGenerator_double_commutator A hA]
  simp only [matrixFrobeniusPair,Matrix.mul_smul,Matrix.trace_smul]
  ring

end InvariantIsing

end

end OAI
