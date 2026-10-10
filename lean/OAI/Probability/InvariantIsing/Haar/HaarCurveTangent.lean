import OAI.Probability.InvariantIsing.Haar.HaarDirectionBound
import OAI.Probability.InvariantIsing.Haar.SpecialPlaneRotation

namespace OAI

/-! The velocity of an actual orthogonal curve is a skew left tangent. -/
noncomputable section
open Matrix MvPolynomial
open scoped BigOperators
namespace InvariantIsing

lemma orthogonalCurve_tangent_skew {N : ℕ} (U : ℝ → SpecialOrthogonal N)
    (B : Matrix (Fin N) (Fin N) ℝ) (t : ℝ)
    (hB : ∀ i j, HasDerivAt (fun s => (U s : Matrix (Fin N) (Fin N) ℝ) i j) (B i j) t) :
    (B*(U t : Matrix (Fin N) (Fin N) ℝ).transpose).transpose =
      -(B*(U t : Matrix (Fin N) (Fin N) ℝ).transpose) := by
  have hm (s : ℝ) := (Matrix.mem_orthogonalGroup_iff (Fin N) ℝ).mp
    (Matrix.mem_specialOrthogonalGroup_iff.mp (U s).property).1
  have hz (i j : Fin N) :
      (∑ k, (B i k*(U t : Matrix (Fin N) (Fin N) ℝ) j k+
        (U t : Matrix (Fin N) (Fin N) ℝ) i k*B j k)) = 0 := by
    have hd := HasDerivAt.fun_sum (u := Finset.univ) fun k _ => (hB i k).mul (hB j k)
    have he : (fun s => ∑ k, (U s : Matrix (Fin N) (Fin N) ℝ) i k*
        (U s : Matrix (Fin N) (Fin N) ℝ) j k) =
        fun _ : ℝ => (1 : Matrix (Fin N) (Fin N) ℝ) i j := by
      funext s
      exact congrFun (congrFun (hm s) i) j
    change HasDerivAt (fun s => ∑ k, (U s : Matrix (Fin N) (Fin N) ℝ) i k*
      (U s : Matrix (Fin N) (Fin N) ℝ) j k) _ t at hd
    rw [he] at hd
    exact hd.unique (hasDerivAt_const t _)
  have hadd : B*(U t : Matrix (Fin N) (Fin N) ℝ).transpose+
      (U t : Matrix (Fin N) (Fin N) ℝ)*B.transpose=0 := by
    ext i j
    simpa only [Matrix.add_apply,Matrix.mul_apply,Matrix.transpose_apply,
      Matrix.zero_apply,Finset.sum_add_distrib] using hz i j
  rw [Matrix.transpose_mul,Matrix.transpose_transpose]
  apply eq_neg_iff_add_eq_zero.mpr
  simpa only [add_comm] using hadd

lemma orthogonalCurve_tangent_mul {N : ℕ} (U : SpecialOrthogonal N)
    (B : Matrix (Fin N) (Fin N) ℝ) :
    (B*(U : Matrix (Fin N) (Fin N) ℝ).transpose)*(U : Matrix (Fin N) (Fin N) ℝ) = B := by
  rw [mul_assoc,(Matrix.mem_orthogonalGroup_iff' (Fin N) ℝ).mp
    (Matrix.mem_specialOrthogonalGroup_iff.mp U.property).1,mul_one]

lemma orthogonalCurve_polynomial_derivative {N : ℕ} (p : MatrixPolynomial N)
    (U : ℝ → SpecialOrthogonal N) (B : Matrix (Fin N) (Fin N) ℝ) (t : ℝ)
    (hB : ∀ i j, HasDerivAt (fun s => (U s : Matrix (Fin N) (Fin N) ℝ) i j) (B i j) t) :
    HasDerivAt (fun s => matrixPolynomialEval (U s : Matrix (Fin N) (Fin N) ℝ) p)
      (matrixPolynomialEval (U t : Matrix (Fin N) (Fin N) ℝ)
        (matrixPolynomialDerivation (B*(U t : Matrix (Fin N) (Fin N) ℝ).transpose) p)) t := by
  apply hasDerivAt_matrixPolynomialEval
  intro i j
  rw [orthogonalCurve_tangent_mul]
  exact hB i j

end InvariantIsing

end

end OAI
