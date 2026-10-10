import OAI.Probability.InvariantIsing.Haar.HaarPlaneSandwich

namespace OAI

/-! Exact orthogonal Lie-algebra contractions in the unnormalized Frobenius convention. -/
noncomputable section
open Matrix
open scoped BigOperators
namespace InvariantIsing

lemma sum_planeGenerator_sq {N : ℕ} :
    (∑ i : Fin N, ∑ j : Fin N, planeGenerator i j*planeGenerator i j) =
      (-2*((N : ℝ)-1)) • (1 : Matrix (Fin N) (Fin N) ℝ) := by
  have h := sum_planeGenerator_sandwich (1 : Matrix (Fin N) (Fin N) ℝ)
  simp only [mul_one,transpose_one,trace_one,Fintype.card_fin] at h
  rw [h]
  module

lemma skew_matrix_trace_zero {N : ℕ} {A : Matrix (Fin N) (Fin N) ℝ}
    (hA : A.transpose = -A) : A.trace = 0 := by
  have h := congrArg Matrix.trace hA
  rw [Matrix.trace_transpose,Matrix.trace_neg] at h
  linarith

theorem sum_planeGenerator_double_commutator {N : ℕ}
    (A : Matrix (Fin N) (Fin N) ℝ) (hA : A.transpose = -A) :
    (∑ i : Fin N, ∑ j : Fin N,
      (planeGenerator i j*(planeGenerator i j*A-A*planeGenerator i j)-
        (planeGenerator i j*A-A*planeGenerator i j)*planeGenerator i j)) =
      (-4*((N : ℝ)-2)) • A := by
  have he (i j : Fin N) :
      planeGenerator i j*(planeGenerator i j*A-A*planeGenerator i j)-
        (planeGenerator i j*A-A*planeGenerator i j)*planeGenerator i j =
      (planeGenerator i j*planeGenerator i j)*A-
        (2 : ℝ) • (planeGenerator i j*A*planeGenerator i j)+
        A*(planeGenerator i j*planeGenerator i j) := by
    simp only [two_smul]
    noncomm_ring
  simp_rw [he,Finset.sum_add_distrib,Finset.sum_sub_distrib]
  have hl : (∑ i : Fin N, ∑ j : Fin N, (planeGenerator i j*planeGenerator i j)*A) =
      (∑ i : Fin N, ∑ j : Fin N, planeGenerator i j*planeGenerator i j)*A := by
    simp only [Finset.sum_mul]
  have hr : (∑ i : Fin N, ∑ j : Fin N, A*(planeGenerator i j*planeGenerator i j)) =
      A*(∑ i : Fin N, ∑ j : Fin N, planeGenerator i j*planeGenerator i j) := by
    simp only [Finset.mul_sum]
  have hm : (∑ i : Fin N, ∑ j : Fin N, (2 : ℝ) • (planeGenerator i j*A*planeGenerator i j)) =
      (2 : ℝ) • (∑ i : Fin N, ∑ j : Fin N, planeGenerator i j*A*planeGenerator i j) := by
    simp only [Finset.smul_sum]
  rw [hl,hr,hm,sum_planeGenerator_sq,sum_planeGenerator_sandwich,hA,skew_matrix_trace_zero hA]
  simp only [mul_zero,zero_smul,sub_zero,smul_mul_assoc,mul_smul_comm,one_mul,mul_one]
  module

end InvariantIsing

end

end OAI
