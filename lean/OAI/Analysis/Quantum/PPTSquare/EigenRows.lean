import Mathlib.LinearAlgebra.Eigenspace.Charpoly
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic.LinearCombination

namespace OAI

noncomputable section
open scoped BigOperators Matrix
open Polynomial Matrix
namespace EigenRows
variable {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι]

lemma exists_eigenrows (A : Matrix ι ι K) (r : ι → K) (hr : Function.Injective r)
    (hf : A.charpoly = ∏ i, (X - C (r i))) :
    ∃ S : Matrix ι ι K, IsUnit S ∧ S * A = diagonal r * S := by
  classical
  have he (i : ι) : Module.End.HasEigenvalue A.transpose.toLin' (r i) := by
    rw [Module.End.hasEigenvalue_iff_isRoot_charpoly, Matrix.charpoly_toLin', Matrix.charpoly_transpose, hf]
    simp only [Polynomial.IsRoot.def, Polynomial.eval_prod, Polynomial.eval_sub,
      Polynomial.eval_X, Polynomial.eval_C]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (sub_self _)
  choose v hv using fun i => (he i).exists_hasEigenvector
  have hi : LinearIndependent K v :=
    Module.End.eigenvectors_linearIndependent' _ r hr v hv
  let S : Matrix ι ι K := v
  refine ⟨S, Matrix.linearIndependent_rows_iff_isUnit.mp hi, ?_⟩
  ext i j
  have h := congrFun (hv i).apply_eq_smul j
  rw [Matrix.mul_apply, Matrix.diagonal_mul]
  change (∑ k, v i k * A k j) = r i * v i j
  simpa only [Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Matrix.transpose_apply,
    Pi.smul_apply, smul_eq_mul, mul_comm] using h

lemma diagonal_of_commute (r : ι → K) (hr : Function.Injective r) (T : Matrix ι ι K)
    (h : diagonal r * T = T * diagonal r) : T = diagonal (fun i => T i i) := by
  ext i j
  by_cases hij : i = j
  · subst j; simp
  · simp only [Matrix.diagonal_apply, ite_eq_right hij]
    have hh := congrFun (congrFun h i) j
    simp only [Matrix.diagonal_mul, Matrix.mul_diagonal] at hh
    have hz : (r i - r j) * T i j = 0 := by linear_combination hh
    exact (mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr (hr.ne hij))

lemma simultaneous (A B S : Matrix ι ι K) (r : ι → K) (hr : Function.Injective r)
    (hS : IsUnit S) (he : S * A = diagonal r * S) (hAB : A * B = B * A) :
    ∃ t : ι → K, S * B = diagonal t * S := by
  have hs := (Matrix.isUnit_iff_isUnit_det S).mp hS
  have hAS : A * S⁻¹ = S⁻¹ * diagonal r := by
    have h := congrArg (fun T => S⁻¹ * T * S⁻¹) he
    simpa only [Matrix.nonsing_inv_mul_cancel_left _ _ hs,
      mul_assoc, Matrix.mul_nonsing_inv S hs, mul_one] using h
  let T := S * B * S⁻¹
  have hD : diagonal r * T = T * diagonal r := by
    calc
      diagonal r * T = (diagonal r * S) * B * S⁻¹ := by simp only [T, mul_assoc]
      _ = (S * A) * B * S⁻¹ := by rw [he]
      _ = S * (B * A) * S⁻¹ := by rw [mul_assoc S A B, hAB]
      _ = S * B * (A * S⁻¹) := by simp only [mul_assoc]
      _ = T * diagonal r := by rw [hAS]; simp only [T, mul_assoc]
  refine ⟨fun i => T i i, ?_⟩
  rw [← diagonal_of_commute r hr T hD]
  exact (Matrix.nonsing_inv_mul_cancel_right S (S * B) hs).symm

lemma row_scalar (S A : Matrix ι ι K) (r : ι → K) (hr : Function.Injective r)
    (hS : IsUnit S) (he : S * A = diagonal r * S)
    (i : ι) (v : ι → K) (hv : v ᵥ* A = r i • v) :
    ∃ c : K, v = c • S.row i := by
  classical
  have hs := (Matrix.isUnit_iff_isUnit_det S).mp hS
  let w := v ᵥ* S⁻¹
  have hwS : w ᵥ* S = v := by
    simp only [w, Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul S hs, Matrix.vecMul_one]
  have hw : w ᵥ* diagonal r = r i • w := by
    have h := congrArg (fun z => z ᵥ* S⁻¹) hv
    rw [← hwS] at h
    simp only [Matrix.vecMul_vecMul, he, Matrix.mul_nonsing_inv S hs,
      Matrix.smul_vecMul] at h
    simpa only [Matrix.vecMul_vecMul, mul_assoc, Matrix.mul_nonsing_inv S hs, mul_one, Matrix.vecMul_one] using h
  have hz (j : ι) (hj : j ≠ i) : w j = 0 := by
    have h := congrFun hw j
    simp only [Matrix.vecMul_diagonal, Pi.smul_apply, smul_eq_mul] at h
    have hh : (r j-r i)*w j=0 := by linear_combination h
    exact (mul_eq_zero.mp hh).resolve_left (sub_ne_zero.mpr (hr.ne hj))
  refine ⟨w i, ?_⟩
  rw [← hwS]
  ext j
  simp only [Matrix.vecMul, dotProduct, Pi.smul_apply, smul_eq_mul, Matrix.row_apply]
  rw [Finset.sum_eq_single i]
  · intro b _ hb; rw [hz b hb, zero_mul]
  · simp

lemma normalized_row_unique (S A : Matrix ι ι K) (r : ι → K) (hr : Function.Injective r)
    (hS : IsUnit S) (he : S * A = diagonal r * S) (z : ι) (hz : ∀ i, S i z = 1)
    (i : ι) (v : ι → K) (hv : v ᵥ* A = r i • v) (hvz : v z = 1) :
    v = S.row i := by
  obtain ⟨c,hc⟩ := row_scalar S A r hr hS he i v hv
  have h := congrFun hc z
  simp only [Pi.smul_apply, smul_eq_mul, Matrix.row_apply, hz, mul_one, hvz] at h
  rw [hc, ← h, one_smul]
end EigenRows

end

end OAI
