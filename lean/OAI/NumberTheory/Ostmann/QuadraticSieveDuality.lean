import OAI.NumberTheory.Ostmann.QuadraticSieveNorm

namespace OAI

namespace Ostmann.QuadraticSieve
open scoped Matrix.Norms.L2Operator

noncomputable def matrixEnergy {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : Matrix ι κ ℂ) (a : κ → ℂ) : ℝ :=
  ∑ i, ‖∑ j, A i j * a j‖ ^ 2

theorem matrixEnergy_eq_norm_sq {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (A : Matrix ι κ ℂ) (x : EuclideanSpace ℂ κ) :
    matrixEnergy A x = ‖A.toEuclideanLin x‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  rfl

theorem matrix_norm_sq_le_of_bound {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (A : Matrix ι κ ℂ) {K : ℝ} (hK : 0 ≤ K)
    (h : ∀ a : κ → ℂ, matrixEnergy A a ≤ K * ∑ j, ‖a j‖ ^ 2) :
    ‖A‖ ^ 2 ≤ K := by
  let T : EuclideanSpace ℂ κ →L[ℂ] EuclideanSpace ℂ ι := A.toEuclideanLin.toContinuousLinearMap
  have hT : ‖T‖ ≤ Real.sqrt K := by
    apply ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _)
    intro x
    have hx := h x
    rw [matrixEnergy_eq_norm_sq, ← EuclideanSpace.norm_sq_eq x] at hx
    apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
    simpa only [T, LinearMap.coe_toContinuousLinearMap', mul_pow, Real.sq_sqrt hK] using hx
  have hp := pow_le_pow_left₀ (norm_nonneg T) hT 2
  simpa only [Matrix.l2_opNorm_def, LinearEquiv.trans_apply, T, Real.sq_sqrt hK] using hp

theorem matrixEnergy_le_of_norm_sq {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (A : Matrix ι κ ℂ) {K : ℝ} (hK : ‖A‖ ^ 2 ≤ K) (a : κ → ℂ) :
    matrixEnergy A a ≤ K * ∑ j, ‖a j‖ ^ 2 := by
  let x : EuclideanSpace ℂ κ := WithLp.toLp 2 a
  let T : EuclideanSpace ℂ κ →L[ℂ] EuclideanSpace ℂ ι := A.toEuclideanLin.toContinuousLinearMap
  calc
    matrixEnergy A a = ‖T x‖ ^ 2 := matrixEnergy_eq_norm_sq A x
    _ ≤ (‖T‖ * ‖x‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (T.le_opNorm x) 2
    _ = ‖A‖ ^ 2 * ∑ j, ‖a j‖ ^ 2 := by
      rw [mul_pow, EuclideanSpace.norm_sq_eq]
      rfl
    _ ≤ K * ∑ j, ‖a j‖ ^ 2 :=
      mul_le_mul_of_nonneg_right hK (Finset.sum_nonneg (fun _ _ => sq_nonneg _))

theorem matrix_energy_duality {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (A : Matrix ι κ ℂ) {K : ℝ} (hK : 0 ≤ K)
    (h : ∀ a : κ → ℂ, matrixEnergy A a ≤ K * ∑ j, ‖a j‖ ^ 2) (b : ι → ℂ) :
    matrixEnergy A.conjTranspose b ≤ K * ∑ i, ‖b i‖ ^ 2 := by
  apply matrixEnergy_le_of_norm_sq
  rw [Matrix.l2_opNorm_conjTranspose]
  exact matrix_norm_sq_le_of_bound A hK h

end Ostmann.QuadraticSieve

end OAI
