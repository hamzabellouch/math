import OAI.Probability.InvariantIsing.Haar.HaarPolynomialKernel
import OAI.Probability.InvariantIsing.Haar.HaarPlaneFrame

namespace OAI

/-! The averaging kernel peaks exactly at coincident orthogonal matrices. -/
noncomputable section
open Matrix MvPolynomial MeasureTheory
open scoped BigOperators
namespace InvariantIsing

lemma specialOrthogonal_sum_sq {N : ℕ} (U : SpecialOrthogonal N) :
    (∑ i, ∑ j, ((U : Matrix (Fin N) (Fin N) ℝ) i j)^2) = N := by
  rw [← matrixFrobeniusPair_self]
  unfold matrixFrobeniusPair
  rw [(Matrix.mem_orthogonalGroup_iff' (Fin N) ℝ).mp
    (Matrix.mem_specialOrthogonalGroup_iff.mp U.property).1]
  simp

lemma haarKernelBase_dist {N : ℕ} (U V : SpecialOrthogonal N) :
    haarKernelBase U V = 2*N-(frobeniusDistance U V)^2/2 := by
  have hU := specialOrthogonal_sum_sq U
  have hV := specialOrthogonal_sum_sq V
  rw [frobeniusDistance,Real.sq_sqrt (Finset.sum_nonneg fun i _ =>
    Finset.sum_nonneg fun j _ => sq_nonneg _)]
  have hsum : (∑ i, ∑ j, ((U : Matrix (Fin N) (Fin N) ℝ) i j-
      (V : Matrix (Fin N) (Fin N) ℝ) i j)^2) = 2*N-
      2*(∑ i, ∑ j, (U : Matrix (Fin N) (Fin N) ℝ) i j*
        (V : Matrix (Fin N) (Fin N) ℝ) i j) := by
    simp only [sub_sq,Finset.sum_add_distrib,Finset.sum_sub_distrib]
    simp_rw [mul_assoc,← Finset.mul_sum]
    rw [hU,hV]
    ring
  rw [hsum]
  unfold haarKernelBase
  ring

lemma haarKernelBase_nonneg {N : ℕ} (U V : SpecialOrthogonal N) :
    0 ≤ haarKernelBase U V := by
  have h := Finset.sum_nonneg (s := Finset.univ) (fun i _ =>
    Finset.sum_nonneg (s := Finset.univ) (fun j _ =>
      sq_nonneg ((U : Matrix (Fin N) (Fin N) ℝ) i j+
        (V : Matrix (Fin N) (Fin N) ℝ) i j)))
  simp only [add_sq,Finset.sum_add_distrib] at h
  simp_rw [mul_assoc,← Finset.mul_sum] at h
  rw [specialOrthogonal_sum_sq U,specialOrthogonal_sum_sq V] at h
  unfold haarKernelBase
  linarith

lemma haarKernelBase_le {N : ℕ} (U V : SpecialOrthogonal N) :
    haarKernelBase U V ≤ 2*N := by
  rw [haarKernelBase_dist]
  nlinarith [sq_nonneg (frobeniusDistance U V)]

lemma haarKernelBase_self {N : ℕ} (U : SpecialOrthogonal N) :
    haarKernelBase U U = 2*N := by
  unfold haarKernelBase
  simp_rw [← pow_two]
  rw [specialOrthogonal_sum_sq]
  ring

lemma haarKernelBase_mul_left {N : ℕ} (W U V : SpecialOrthogonal N) :
    haarKernelBase (W*U) (W*V) = haarKernelBase U V := by
  have he : matrixFrobeniusPair
      ((W : Matrix (Fin N) (Fin N) ℝ)*(U : Matrix (Fin N) (Fin N) ℝ))
      ((W : Matrix (Fin N) (Fin N) ℝ)*(V : Matrix (Fin N) (Fin N) ℝ)) =
      matrixFrobeniusPair (U : Matrix (Fin N) (Fin N) ℝ)
        (V : Matrix (Fin N) (Fin N) ℝ) := by
    unfold matrixFrobeniusPair
    rw [Matrix.transpose_mul,mul_assoc,← mul_assoc (W : Matrix (Fin N) (Fin N) ℝ).transpose,
      (Matrix.mem_orthogonalGroup_iff' (Fin N) ℝ).mp
        (Matrix.mem_specialOrthogonalGroup_iff.mp W.property).1,one_mul]
  unfold haarKernelBase
  rw [← matrixFrobeniusPair_eq_sum,← matrixFrobeniusPair_eq_sum]
  exact congrArg (fun x : ℝ => N+x) he

lemma haarKernelBase_mul_right {N : ℕ} (U V W : SpecialOrthogonal N) :
    haarKernelBase (U*W) (V*W) = haarKernelBase U V := by
  have he : matrixFrobeniusPair
      ((U : Matrix (Fin N) (Fin N) ℝ)*(W : Matrix (Fin N) (Fin N) ℝ))
      ((V : Matrix (Fin N) (Fin N) ℝ)*(W : Matrix (Fin N) (Fin N) ℝ)) =
      matrixFrobeniusPair (U : Matrix (Fin N) (Fin N) ℝ)
        (V : Matrix (Fin N) (Fin N) ℝ) := by
    unfold matrixFrobeniusPair
    rw [Matrix.transpose_mul,Matrix.trace_mul_cycle]
    rw [mul_assoc (V : Matrix (Fin N) (Fin N) ℝ) W (W : Matrix (Fin N) (Fin N) ℝ).transpose,
      (Matrix.mem_orthogonalGroup_iff (Fin N) ℝ).mp
        (Matrix.mem_specialOrthogonalGroup_iff.mp W.property).1,mul_one,Matrix.trace_mul_comm]
  unfold haarKernelBase
  rw [← matrixFrobeniusPair_eq_sum,← matrixFrobeniusPair_eq_sum]
  exact congrArg (fun x : ℝ => N+x) he

end InvariantIsing

end

end OAI
