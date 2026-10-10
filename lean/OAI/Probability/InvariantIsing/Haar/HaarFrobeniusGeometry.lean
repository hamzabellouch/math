import OAI.Probability.InvariantIsing.Haar.HaarKernelGeometry

namespace OAI

/-! Unnormalized Frobenius geometry for the averaging and tangent estimates. -/
noncomputable section
open Matrix
open scoped BigOperators Matrix.Norms.Frobenius
namespace InvariantIsing

lemma frobenius_norm_sq {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ) :
    ‖A‖^2 = matrixFrobeniusPair A A := by
  rw [Matrix.frobenius_norm_def]
  simp only [Real.rpow_two,Real.norm_eq_abs,sq_abs]
  have hs : 0 ≤ ∑ i : Fin N, ∑ j : Fin N, (A i j)^2 :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _
  rw [← Real.sqrt_eq_rpow,Real.sq_sqrt hs,matrixFrobeniusPair_self]

lemma frobeniusDistance_eq_norm {N : ℕ} (U V : SpecialOrthogonal N) :
    frobeniusDistance U V = ‖(U : Matrix (Fin N) (Fin N) ℝ)-V‖ := by
  rw [Matrix.frobenius_norm_def]
  simp only [Real.rpow_two,Real.norm_eq_abs,sq_abs,Matrix.sub_apply]
  exact Real.sqrt_eq_rpow _

lemma frobenius_norm_mul_orthogonal {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ)
    (U : SpecialOrthogonal N) : ‖A*(U : Matrix (Fin N) (Fin N) ℝ)‖ = ‖A‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [frobenius_norm_sq,frobenius_norm_sq]
  unfold matrixFrobeniusPair
  rw [Matrix.transpose_mul,Matrix.trace_mul_cycle]
  rw [mul_assoc A U (U : Matrix (Fin N) (Fin N) ℝ).transpose,
    (Matrix.mem_orthogonalGroup_iff (Fin N) ℝ).mp
      (Matrix.mem_specialOrthogonalGroup_iff.mp U.property).1,mul_one,Matrix.trace_mul_comm]

lemma frobeniusDistance_mul_left {N : ℕ} (W U V : SpecialOrthogonal N) :
    frobeniusDistance (W*U) (W*V) = frobeniusDistance U V := by
  have h := congrArg (fun x : ℝ => 2*N-x) (haarKernelBase_mul_left W U V)
  rw [haarKernelBase_dist,haarKernelBase_dist] at h
  apply (sq_eq_sq₀ (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)).mp
  change (frobeniusDistance (W*U) (W*V))^2 = (frobeniusDistance U V)^2
  linarith

lemma frobeniusDistance_comm {N : ℕ} (U V : SpecialOrthogonal N) :
    frobeniusDistance U V = frobeniusDistance V U := by
  rw [frobeniusDistance_eq_norm,frobeniusDistance_eq_norm,← norm_neg,neg_sub]

lemma frobeniusDistance_mul_right {N : ℕ} (U V W : SpecialOrthogonal N) :
    frobeniusDistance (U*W) (V*W) = frobeniusDistance U V := by
  rw [frobeniusDistance_eq_norm,frobeniusDistance_eq_norm]
  change ‖(U : Matrix (Fin N) (Fin N) ℝ)*W-(V : Matrix (Fin N) (Fin N) ℝ)*W‖ = _
  rw [← sub_mul,frobenius_norm_mul_orthogonal]

end InvariantIsing

end

end OAI
