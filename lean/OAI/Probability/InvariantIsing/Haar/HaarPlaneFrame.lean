import OAI.Probability.InvariantIsing.Haar.HaarFrobeniusBracket

namespace OAI

/-! Exact coordinate-plane frame identities in the skew matrix space. -/
noncomputable section
open Matrix
open scoped BigOperators
namespace InvariantIsing

lemma planeGenerator_swap {N : ℕ} (i j : Fin N) :
    planeGenerator j i = -planeGenerator i j := by
  simp only [planeGenerator,neg_sub]

lemma sum_entry_planeGenerator {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ) :
    (∑ i, ∑ j, A i j • planeGenerator i j) = A-A.transpose := by
  classical
  ext k l
  simp only [Matrix.sum_apply,Matrix.sub_apply,Matrix.smul_apply,smul_eq_mul,
    planeGenerator,Matrix.single_apply,mul_sub,Finset.sum_sub_distrib]
  simp [ite_and,Matrix.transpose_apply]

lemma matrixFrobeniusPair_eq_sum {N : ℕ} (A B : Matrix (Fin N) (Fin N) ℝ) :
    matrixFrobeniusPair A B = ∑ i, ∑ j, A i j*B i j := by
  simp only [matrixFrobeniusPair,Matrix.trace,Matrix.diag_apply,Matrix.mul_apply,
    Matrix.transpose_apply]
  exact Finset.sum_comm

lemma matrixFrobeniusPair_plane {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ) (i j : Fin N) :
    matrixFrobeniusPair A (planeGenerator i j) = A i j-A j i := by
  classical
  rw [matrixFrobeniusPair_eq_sum]
  simp [planeGenerator,Matrix.single_apply,Matrix.sub_apply,mul_sub,
    Finset.sum_sub_distrib,ite_and]

lemma skew_matrix_bracket {N : ℕ} {A B : Matrix (Fin N) (Fin N) ℝ}
    (hA : A.transpose = -A) (hB : B.transpose = -B) :
    (A*B-B*A).transpose = -(A*B-B*A) := by
  simp only [Matrix.transpose_sub,Matrix.transpose_mul,hA,hB,neg_mul_neg,neg_sub]

lemma matrixFrobeniusPair_plane_skew {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ)
    (hA : A.transpose = -A) (i j : Fin N) :
    matrixFrobeniusPair A (planeGenerator i j) = 2*A i j := by
  have h : A j i = -A i j := congrFun (congrFun hA i) j
  rw [matrixFrobeniusPair_plane,h]
  ring

lemma sum_matrixFrobeniusPair_plane_sq {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ)
    (hA : A.transpose = -A) :
    (∑ i, ∑ j, (matrixFrobeniusPair A (planeGenerator i j))^2) =
      4*matrixFrobeniusPair A A := by
  simp_rw [matrixFrobeniusPair_plane_skew A hA]
  rw [matrixFrobeniusPair_self]
  simp only [mul_pow,show (2:ℝ)^2=4 by norm_num,Finset.mul_sum]

/-- A linear functional on skew matrices is represented by its plane coordinates. -/
lemma plane_functional_representation {N : ℕ}
    (ell : Matrix (Fin N) (Fin N) ℝ →ₗ[ℝ] ℝ)
    (B : Matrix (Fin N) (Fin N) ℝ) (hB : B.transpose = -B) :
    matrixFrobeniusPair (Matrix.of fun i j => ell (planeGenerator i j)) B = 2*ell B := by
  have h := congrArg ell (sum_entry_planeGenerator B)
  simp only [map_sum,map_smul,map_sub,hB,map_neg,smul_eq_mul] at h
  rw [matrixFrobeniusPair_eq_sum]
  calc
    (∑ i, ∑ j, ell (planeGenerator i j)*B i j) =
        ∑ i, ∑ j, B i j*ell (planeGenerator i j) := by
      apply Finset.sum_congr rfl; intro i _
      apply Finset.sum_congr rfl; intro j _; ring
    _ = 2*ell B := by linarith

end InvariantIsing

end

end OAI
