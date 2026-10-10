import Mathlib
import OAI.Analysis.AffineBernstein.NewtonBasis
import OAI.Analysis.AffineBernstein.BilinearNewton
import OAI.Analysis.AffineBernstein.ConjugationNewton

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

open scoped Matrix
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
lemma bilinearOfMatrix_reconstruct (b : OrthonormalBasis ι ℝ E)
    (T : E →L[ℝ] E →L[ℝ] ℝ) (v w : E) :
    bilinearOfMatrix b (Matrix.of fun i j => T (b i) (b j)) v w = T v w := by
  rw [bilinearOfMatrix_apply]
  simp only [Matrix.of_apply]
  conv_rhs => rw [← b.sum_repr' v, ← b.sum_repr' w]
  simp only [map_sum, map_smul, sum_apply, smul_apply, smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

omit [DecidableEq ι] in
lemma bilinearOfMatrix_change (b c : OrthonormalBasis ι ℝ E)
    (A : Matrix ι ι ℝ) (i j : ι) :
    bilinearOfMatrix b A (c i) (c j) =
      ((orthogonalChange b c)ᵀ * A * orthogonalChange b c) i j := by
  rw [bilinearOfMatrix_apply]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, orthogonalChange, Matrix.of_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro l _
  apply Finset.sum_congr rfl
  intro k _
  ring

omit [DecidableEq ι] in
lemma basisHessian_change (b c : OrthonormalBasis ι ℝ E) (H : E → ℝ) (x : E) :
    basisHessian c H x = (orthogonalChange b c)ᵀ * basisHessian b H x * orthogonalChange b c := by
  ext i j
  have hh := bilinearOfMatrix_change b c (basisHessian b H x) i j
  exact (bilinearOfMatrix_reconstruct b (fderiv ℝ (fderiv ℝ H) x) (c i) (c j)).symm.trans hh

lemma supportNewtonTensor_change (b c : OrthonormalBasis ι ℝ E) (H : E → ℝ) (x : E)
    (i j : ι) : supportNewtonTensor b H x (c i) (c j) =
      newtonTensor (basisHessian c H x) i j := by
  rw [supportNewtonTensor, bilinearOfMatrix_change, basisHessian_change b c,
    newtonTensor_conjugate_orthogonal (orthogonalChange_mul_transpose b c)
      (orthogonalChange_transpose_mul b c)]

/- In every orthonormal frame adapted to the unit normal, the global tensor
is EXACTLY the cofactor of the tangential ambient Hessian. The empty tangential
block causes no exception. -/
theorem supportNewtonTensor_eq_tangential_cofactor
    (b c : OrthonormalBasis (ι ⊕ Unit) ℝ E) {H : E → ℝ} {e : E}
    (hH : ContDiffAt ℝ ∞ H e) (hc : c (Sum.inr ()) = e)
    (hr : ∀ v, fderiv ℝ (fderiv ℝ H) e v e = 0) (i j : ι) :
    supportNewtonTensor b H e (c (Sum.inl i)) (c (Sum.inl j)) =
      (Matrix.of fun l m : ι => fderiv ℝ (fderiv ℝ H) e
        (c (Sum.inl l)) (c (Sum.inl m))).adjugate i j := by
  rw [supportNewtonTensor_change b c]
  have hs := hH.isSymmSndFDerivAt (by simp)
  have hb : basisHessian c H e = Matrix.fromBlocks
      (Matrix.of fun l m : ι => fderiv ℝ (fderiv ℝ H) e (c (Sum.inl l)) (c (Sum.inl m)))
      0 0 (0 : Matrix Unit Unit ℝ) := by
    ext l m
    cases l with
    | inl l =>
      cases m with
      | inl m => rfl
      | inr m => cases m; simp only [basisHessian, hc, hr, Matrix.fromBlocks_apply₁₂, Matrix.zero_apply]
    | inr l =>
      cases l
      cases m with
      | inl m => simp only [basisHessian, hc, hs.eq e, hr, Matrix.fromBlocks_apply₂₁, Matrix.zero_apply]
      | inr m => cases m; simp only [basisHessian, hc, hr, Matrix.fromBlocks_apply₂₂, Matrix.zero_apply]
  rw [hb, newtonTensor_fromBlocks_zero]

end AffineBernstein
end

end OAI
