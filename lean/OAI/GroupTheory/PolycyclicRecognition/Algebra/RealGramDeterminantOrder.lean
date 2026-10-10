import Mathlib.Analysis.Matrix.Order
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Tactic.Lift
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace OAI

/-! # Monotonicity of the positive Gram determinant

The concrete real-matrix form needed for expanding word-ball evaluations.
-/
noncomputable section
namespace PolycyclicRecognition
open Matrix
open scoped MatrixOrder
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem real_matrix_eigenvalues_ge_one {A : Matrix ι ι ℝ} (hherm : A.IsHermitian)
    (hA : (A - 1).PosSemidef) (i : ι) : 1 ≤ hherm.eigenvalues i := by
    let v := hherm.eigenvectorBasis i
    have hv : (star (v : ι → ℝ)) ⬝ᵥ (v : ι → ℝ) = 1 := by
      rw [dotProduct_comm, ← EuclideanSpace.inner_eq_star_dotProduct]
      dsimp only [v]
      simp only [inner_self_eq_norm_sq_to_K, hherm.eigenvectorBasis.orthonormal.1 i,
        one_pow, RCLike.ofReal_one]
    have hp := hA.dotProduct_mulVec_nonneg (v : ι → ℝ)
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, dotProduct_sub, hv] at hp
    have hx : (star (v : ι → ℝ)) ⬝ᵥ (A *ᵥ (v : ι → ℝ)) = hherm.eigenvalues i := by
      simpa only [RCLike.re_to_real] using (hherm.eigenvalues_eq i).symm
    rw [hx] at hp
    exact sub_nonneg.mp hp
theorem real_matrix_det_ge_one {A : Matrix ι ι ℝ} (hA : (A - 1).PosSemidef) :
    1 ≤ A.det := by
  have hherm : A.IsHermitian := by
    have h := hA.isHermitian.add (Matrix.isHermitian_one : (1 : Matrix ι ι ℝ).IsHermitian)
    simpa using h
  rw [hherm.det_eq_prod_eigenvalues]
  simpa using Finset.prod_le_prod₀ (fun i _ => (by norm_num : (0 : ℝ) ≤ 1))
    (fun i _ => real_matrix_eigenvalues_ge_one hherm hA i)

theorem real_posDef_det_mono {A B : Matrix ι ι ℝ}
    (hA : A.PosDef) (hAB : (B - A).PosSemidef) : A.det ≤ B.det := by
  obtain ⟨P, hP, hAP⟩ := CStarAlgebra.isStrictlyPositive_iff_eq_star_mul_self.mp
    hA.isStrictlyPositive
  let Q : Matrix ι ι ℝ := P⁻¹
  have hPQ : P * Q = 1 := Matrix.mul_nonsing_inv P
    ((Matrix.isUnit_iff_isUnit_det P).mp hP)
  have hnorm : Qᴴ * A * Q = 1 := by
    rw [hAP, ← star_eq_conjTranspose]
    calc
      _ = (star Q * star P) * (P * Q) := by simp only [mul_assoc]
      _ = star (P * Q) := by rw [star_mul, hPQ, mul_one]
      _ = 1 := by rw [hPQ, star_one]
  have hsub : (Qᴴ * B * Q - 1).PosSemidef := by
    rw [← hnorm, ← sub_mul, ← mul_sub]
    exact hAB.conjTranspose_mul_mul_same Q
  have hdet := real_matrix_det_ge_one hsub
  have hn : Q.det * A.det * Q.det = 1 := by
    simpa only [Matrix.det_mul, Matrix.det_conjTranspose, star_trivial, Matrix.det_one]
      using congrArg Matrix.det hnorm
  have hh : 1 ≤ Q.det * B.det * Q.det := by
    simpa only [Matrix.det_mul, Matrix.det_conjTranspose, star_trivial] using hdet
  have hmul := mul_le_mul_of_nonneg_left hh hA.det_pos.le
  have he : A.det * (Q.det * B.det * Q.det) = B.det := by
    calc
      _ = (Q.det * A.det * Q.det) * B.det := by ring
      _ = B.det := by rw [hn, one_mul]
  simpa only [he, mul_one] using hmul

theorem real_posSemidef_det_mono {A B : Matrix ι ι ℝ}
    (hA : A.PosSemidef) (hAB : (B - A).PosSemidef) : A.det ≤ B.det := by
  by_cases ha : A.det = 0
  · rw [ha]
    have hb : B.PosSemidef := by simpa using hA.add hAB
    exact hb.det_nonneg
  · exact real_posDef_det_mono (hA.posDef_iff_det_ne_zero.mpr ha) hAB

end PolycyclicRecognition

end

end OAI
