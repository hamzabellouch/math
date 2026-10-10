import Mathlib
import OAI.Geometry.PrescribedRicci.HermitianCoercivity
import OAI.Geometry.PrescribedRicci.HermitianTensorEnergy
import OAI.Geometry.PrescribedRicci.MatrixCompactBounds

namespace OAI

/-! Tensor Energy Bounds. -/

noncomputable section
open Matrix
open scoped ComplexOrder MatrixOrder Kronecker Matrix.Norms.Elementwise
namespace MongeAmpere
variable {n m : Type*} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]

omit [DecidableEq n] [DecidableEq m] in
lemma kronecker_norm_le (B : Matrix m m ℂ) (K : Matrix n n ℂ) : ‖B ⊗ₖ K‖ ≤ ‖B‖*‖K‖ := by
  apply matrix_norm_le_of_entries (by positivity)
  intro i j
  rw [Matrix.kronecker_apply,norm_mul]
  exact mul_le_mul (norm_entry_le_entrywise_sup_norm B) (norm_entry_le_entrywise_sup_norm K)
    (norm_nonneg _) (norm_nonneg _)

lemma kronecker_inv {B : Matrix m m ℂ} {K : Matrix n n ℂ} (hB : B.PosDef) (hK : K.PosDef) :
    (B ⊗ₖ K)⁻¹ = B⁻¹ ⊗ₖ K⁻¹ := by
  apply Matrix.inv_eq_right_inv
  rw [← Matrix.mul_kronecker_mul,
    Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hB.det_pos.ne'),
    Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hK.det_pos.ne'),Matrix.one_kronecker_one]

lemma vectorNorm_sq_le_tensorEnergy {B : Matrix m m ℂ} {K : Matrix n n ℂ}
    (hB : B.PosDef) (hK : K.PosDef) (V : m → n → ℂ) (a : m) :
    ‖V a‖^2 ≤ ‖B⁻¹‖*‖K⁻¹‖*(tensorEnergy B K V).re := by
  have hE := tensorEnergy_nonneg hB.posSemidef hK.posSemidef V
  have hbound : ∀ i : n, ‖V a i‖^2 ≤ ‖B⁻¹‖*‖K⁻¹‖*(tensorEnergy B K V).re := by
    intro i
    have h := component_sq_le_hermPair (hB.kronecker hK) (fun p : m × n => V p.1 p.2) (a,i)
    rw [← tensorEnergy_eq,kronecker_inv hB hK] at h
    apply h.trans
    apply mul_le_mul_of_nonneg_right _ hE
    exact (Complex.re_le_norm _).trans ((norm_entry_le_entrywise_sup_norm _).trans
      (kronecker_norm_le _ _))
  have hp : 0 ≤ ‖B⁻¹‖*‖K⁻¹‖*(tensorEnergy B K V).re := by positivity
  have hv : ‖V a‖ ≤ Real.sqrt (‖B⁻¹‖*‖K⁻¹‖*(tensorEnergy B K V).re) := by
    apply (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr
    intro i
    exact (Real.le_sqrt (norm_nonneg _) hp).mpr (hbound i)
  exact ((sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mpr hv).trans_eq (Real.sq_sqrt hp)

end MongeAmpere

end

end OAI
