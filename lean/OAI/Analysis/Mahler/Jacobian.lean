import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace OAI

namespace SymmetricMahler
open Matrix Real

noncomputable def weightedGram {n N : ℕ} (A : Matrix (Fin N) (Fin n) ℝ) (c : Fin N → ℝ) :
    Matrix (Fin n) (Fin n) ℝ := A.transpose * Matrix.diagonal c * A

lemma weightedGram_posSemidef {n N : ℕ} (A : Matrix (Fin N) (Fin n) ℝ)
    {c : Fin N → ℝ} (hc : ∀ j, 0 ≤ c j) : (weightedGram A c).PosSemidef := by
  have h := (Matrix.posSemidef_diagonal_iff.mpr hc).conjTranspose_mul_mul_same A
  simpa only [weightedGram, Matrix.conjTranspose_eq_transpose_of_trivial] using h

lemma weightedGram_det_nonneg {n N : ℕ} (A : Matrix (Fin N) (Fin n) ℝ)
    {c : Fin N → ℝ} (hc : ∀ j, 0 ≤ c j) : 0 ≤ (weightedGram A c).det :=
  (weightedGram_posSemidef A hc).det_nonneg

lemma weightedGram_apply {n N : ℕ} (A : Matrix (Fin N) (Fin n) ℝ)
    (c : Fin N → ℝ) (i k : Fin n) :
    weightedGram A c i k = ∑ j : Fin N, A j i*c j*A j k := by
  unfold weightedGram
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply]

lemma weightedGram_smul {n N : ℕ} (A : Matrix (Fin N) (Fin n) ℝ)
    (c : Fin N → ℝ) (a : ℝ) : weightedGram A (fun j => a*c j) = a • weightedGram A c := by
  ext i k
  simp only [weightedGram_apply, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The x-component is the identity, so arbitrary mixed derivatives in C do
not enter the real determinant. -/
theorem finite_strip_block_jacobian {n N : ℕ} (A : Matrix (Fin N) (Fin n) ℝ)
    (C : Matrix (Fin n) (Fin n) ℝ) {c : Fin N → ℝ} (hc : ∀ j, 0 ≤ c j)
    {m : ℝ} (hm : 0 < m) :
    |(Matrix.fromBlocks (1 : Matrix (Fin n) (Fin n) ℝ) 0 C
      ((4/(Real.pi*m)) • weightedGram A c)).det| =
      (4/(Real.pi*m))^n*(weightedGram A c).det := by
  rw [Matrix.det_fromBlocks_zero₁₂, Matrix.det_one, one_mul, Matrix.det_smul, Fintype.card_fin]
  apply abs_of_nonneg
  exact mul_nonneg (pow_nonneg (by positivity) _) (weightedGram_det_nonneg A hc)

noncomputable def hessianWeight (m : ℝ) (f d : ℂ) : ℝ :=
  m^2*‖f‖^(2*m-2 : ℝ)*‖d‖^2

noncomputable def verticalWeight (m : ℝ) (f d : ℂ) : ℝ :=
  (4*m/Real.pi)*‖f‖^(2*m-2 : ℝ)*‖d‖^2

lemma hessianWeight_nonneg (m : ℝ) (f d : ℂ) : 0 ≤ hessianWeight m f d := by
  unfold hessianWeight
  positivity

lemma verticalWeight_eq_scaled_hessianWeight {m : ℝ} (hm : m ≠ 0) (f d : ℂ) :
    verticalWeight m f d = (4/(Real.pi*m))*hessianWeight m f d := by
  unfold verticalWeight hessianWeight
  field_simp

/-- The Jacobian coefficient for the weights from h and h'.
The only analytic input to this identity is that these are the derivative weights;
positivity and the absolute determinant follow. -/
theorem finite_strip_weighted_jacobian {n N : ℕ} (A : Matrix (Fin N) (Fin n) ℝ)
    (C : Matrix (Fin n) (Fin n) ℝ) (f d : Fin N → ℂ) {m : ℝ} (hm : 0 < m) :
    |(Matrix.fromBlocks (1 : Matrix (Fin n) (Fin n) ℝ) 0 C
      (weightedGram A (fun j => verticalWeight m (f j) (d j)))).det| =
      (4/(Real.pi*m))^n*(weightedGram A (fun j => hessianWeight m (f j) (d j))).det := by
  have hw : (fun j => verticalWeight m (f j) (d j)) =
      fun j => (4/(Real.pi*m))*hessianWeight m (f j) (d j) := by
    funext j
    exact verticalWeight_eq_scaled_hessianWeight hm.ne' _ _
  rw [hw, weightedGram_smul]
  exact finite_strip_block_jacobian A C (fun j => hessianWeight_nonneg _ _ _) hm

end SymmetricMahler

end OAI
