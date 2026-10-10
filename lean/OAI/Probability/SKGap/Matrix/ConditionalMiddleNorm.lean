import Mathlib
import OAI.Probability.SKGap.Localization.DiagonalHessianJoined

namespace OAI

section
noncomputable section
namespace SKGap
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma real_opNorm_add (M N : Matrix ι ι ℝ) : opNorm (M+N) ≤ opNorm M+opNorm N := by
  unfold opNorm
  rw [map_add,map_add]
  exact norm_add_le _ _

lemma real_opNorm_smul (c : ℝ) (M : Matrix ι ι ℝ) : opNorm (c • M)=|c| * opNorm M := by
  unfold opNorm
  rw [map_smul,map_smul,norm_smul,Real.norm_eq_abs]

lemma operator_vecMulVec_le (u v : EuclideanSpace ℝ ι) :
    opNorm (vecMulVec u.ofLp v.ofLp) ≤ ‖u‖*‖v‖ := by
  apply (operator_le_frobenius _).trans
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mp
  rw [Matrix.frobenius_norm_def]
  simp only [Real.rpow_two,← Real.sqrt_eq_rpow]
  rw [Real.sq_sqrt (Finset.sum_nonneg (fun i _=>Finset.sum_nonneg (fun k _=>sq_nonneg _))),
    mul_pow,EuclideanSpace.real_norm_sq_eq,EuclideanSpace.real_norm_sq_eq]
  simp only [vecMulVec_apply,Real.norm_eq_abs,abs_mul,mul_pow,sq_abs]
  rw [Finset.sum_mul]
  apply le_of_eq
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]

lemma operator_mulVec_norm_le (W : Matrix ι ι ℝ) (u : EuclideanSpace ℝ ι) :
    ‖WithLp.toLp 2 (W*ᵥu.ofLp)‖ ≤ opNorm W*‖u‖ := by
  exact W.toEuclideanLin.toContinuousLinearMap.le_opNorm u

lemma goeBilinear_norm_bound (r : ℝ) (u : EuclideanSpace ℝ ι)
    (g : MatrixCoordinates ι → ℝ) :
    |goeBilinear r u.ofLp u.ofLp g| ≤ opNorm (goeMatrix r g)*‖u‖^2 := by
  have hh := matrix_quadratic_op_bound (goeMatrix r g) u.ofLp
  change |goeBilinear r u.ofLp u.ofLp g| ≤ opNorm (goeMatrix r g)*(u.ofLp⬝ᵥu.ofLp) at hh
  convert hh using 1
  rw [EuclideanSpace.real_norm_sq_eq]
  simp only [dotProduct,← sq]

lemma conditionalBlockMatrix_norm {r j q s S a B κ ell : ℝ}
    (u Z : EuclideanSpace ℝ ι) (g : MatrixCoordinates ι → ℝ) (hu : ‖u‖=1) :
    opNorm (conditionalBlockMatrix r j q s S a B κ ell u.ofLp Z.ofLp g) ≤
      (1+2*|κ-1|+|ell-2*κ+1|)*opNorm (goeMatrix r g)+
      2*(|j*sqrt (q/s)| * ‖Z‖+|j*a/s|)+|2*j*(a+B*q)/S| := by
  let W := goeMatrix r g
  let Wu : EuclideanSpace ℝ ι := WithLp.toLp 2 (W*ᵥu.ofLp)
  let w : EuclideanSpace ℝ ι := (j*sqrt (q/s)) • Z-(j*a/s) • u
  have hW : 0 ≤ opNorm W := norm_nonneg _
  have hwu : ‖Wu‖ ≤ opNorm W := by simpa only [hu,mul_one] using operator_mulVec_norm_le W u
  have huu : opNorm (vecMulVec u.ofLp u.ofLp) ≤ 1 := by simpa only [hu,mul_one] using operator_vecMulVec_le u u
  have h1 : opNorm (vecMulVec u.ofLp Wu.ofLp+vecMulVec Wu.ofLp u.ofLp) ≤ 2*opNorm W := by
    apply (real_opNorm_add _ _).trans
    have ha := operator_vecMulVec_le u Wu
    have hb := operator_vecMulVec_le Wu u
    rw [hu,one_mul] at ha
    rw [hu,mul_one] at hb
    linarith
  have hα : |goeBilinear r u.ofLp u.ofLp g| ≤ opNorm W := by
    simpa only [hu,one_pow,mul_one] using goeBilinear_norm_bound r u g
  have hw : ‖w‖ ≤ |j*sqrt (q/s)| * ‖Z‖+|j*a/s| := by
    apply (norm_sub_le _ _).trans
    simp only [norm_smul,Real.norm_eq_abs,hu,mul_one]
    rfl
  have h2 : opNorm (vecMulVec u.ofLp w.ofLp+vecMulVec w.ofLp u.ofLp) ≤
      2*(|j*sqrt (q/s)| * ‖Z‖+|j*a/s|) := by
    apply (real_opNorm_add _ _).trans
    have ha := operator_vecMulVec_le u w
    have hb := operator_vecMulVec_le w u
    rw [hu,one_mul] at ha
    rw [hu,mul_one] at hb
    linarith
  have he : conditionalBlockMatrix r j q s S a B κ ell u.ofLp Z.ofLp g=
      (W+(κ-1) • (vecMulVec u.ofLp Wu.ofLp+vecMulVec Wu.ofLp u.ofLp)+
        ((ell-2*κ+1)*goeBilinear r u.ofLp u.ofLp g) • vecMulVec u.ofLp u.ofLp)+
      (vecMulVec u.ofLp w.ofLp+vecMulVec w.ofLp u.ofLp)+
        (2*j*(a+B*q)/S) • vecMulVec u.ofLp u.ofLp := by
    unfold conditionalBlockMatrix
    rw [goeBlockResidual_expand]
    dsimp [W,Wu,w]
    abel
  rw [he]
  have hn := real_opNorm_add ((W+(κ-1) • (vecMulVec u.ofLp Wu.ofLp+vecMulVec Wu.ofLp u.ofLp)+
        ((ell-2*κ+1)*goeBilinear r u.ofLp u.ofLp g) • vecMulVec u.ofLp u.ofLp)+
      (vecMulVec u.ofLp w.ofLp+vecMulVec w.ofLp u.ofLp)) ((2*j*(a+B*q)/S) • vecMulVec u.ofLp u.ofLp)
  apply hn.trans
  have hd := real_opNorm_add (W+(κ-1) • (vecMulVec u.ofLp Wu.ofLp+vecMulVec Wu.ofLp u.ofLp)+
        ((ell-2*κ+1)*goeBilinear r u.ofLp u.ofLp g) • vecMulVec u.ofLp u.ofLp)
      (vecMulVec u.ofLp w.ofLp+vecMulVec w.ofLp u.ofLp)
  have hc := real_opNorm_add (W+(κ-1) • (vecMulVec u.ofLp Wu.ofLp+vecMulVec Wu.ofLp u.ofLp))
      (((ell-2*κ+1)*goeBilinear r u.ofLp u.ofLp g) • vecMulVec u.ofLp u.ofLp)
  have hb := real_opNorm_add W ((κ-1) • (vecMulVec u.ofLp Wu.ofLp+vecMulVec Wu.ofLp u.ofLp))
  rw [real_opNorm_smul] at hb
  rw [real_opNorm_smul,abs_mul] at hc
  rw [real_opNorm_smul]
  have hp1 := mul_le_mul_of_nonneg_left h1 (abs_nonneg (κ-1))
  have hp2 : |ell-2*κ+1| * |goeBilinear r u.ofLp u.ofLp g| * opNorm (vecMulVec u.ofLp u.ofLp) ≤
      |ell-2*κ+1| * opNorm W := by
    apply (mul_le_mul_of_nonneg_left huu (by positivity)).trans
    rw [mul_one]
    exact mul_le_mul_of_nonneg_left hα (abs_nonneg _)
  have hp3 := mul_le_mul_of_nonneg_left huu (abs_nonneg (2*j*(a+B*q)/S))
  nlinarith only [hd,hc,hb,hp1,hp2,hp3,h2]
end SKGap
end
end

end OAI
