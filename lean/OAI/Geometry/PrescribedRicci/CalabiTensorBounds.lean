import Mathlib
import OAI.Geometry.PrescribedRicci.CalabiTensorAlgebra
import OAI.Geometry.PrescribedRicci.MatrixCompactBounds
import OAI.Geometry.PrescribedRicci.MatrixComponentBounds

namespace OAI

/-! Calabi Tensor Bounds. -/

noncomputable section
open Matrix
open scoped ComplexOrder MatrixOrder Matrix.Norms.Elementwise
namespace MongeAmpere
variable {n : Type*} [Fintype n] [DecidableEq n]

omit [DecidableEq n] in
lemma tensor3_norm_le (L U V : Matrix n n ℂ) :
    ‖tensor3 L U V‖ ≤ ‖L‖*‖U‖*‖V‖ := by
  apply matrix_norm_le_of_entries (by positivity)
  intro i j
  rw [tensor3_apply,norm_mul,norm_mul]
  calc
    _ ≤ ‖L‖*(‖U‖*‖V‖) := mul_le_mul (norm_entry_le_entrywise_sup_norm L)
      (mul_le_mul (norm_entry_le_entrywise_sup_norm U) (norm_entry_le_entrywise_sup_norm V)
        (norm_nonneg _) (norm_nonneg _)) (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (norm_nonneg _)
    _ = _ := by ring

lemma tensorMetric_inv {H : Matrix n n ℂ} (hH : H.PosDef) :
    (tensorMetric H)⁻¹ = tensor3 H.transpose H⁻¹ H.transpose := by
  apply Matrix.inv_eq_right_inv
  rw [tensorMetric,tensor3_mul,← Matrix.transpose_mul,
    Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hH.det_pos.ne'),
    Matrix.transpose_one,tensor3_one]

lemma tensorMetric_norm_bound {H : Matrix n n ℂ} {M : ℝ}
    (hM : 0 ≤ M) (hH : ‖H‖ ≤ M) (hI : ‖H⁻¹‖ ≤ M) : ‖tensorMetric H‖ ≤ M^3 := by
  apply (tensor3_norm_le _ _ _).trans
  rw [Matrix.norm_transpose]
  calc
    _ ≤ M*M*M := mul_le_mul
      (mul_le_mul hI hH (norm_nonneg _) hM) hI (norm_nonneg _) (mul_nonneg hM hM)
    _ = _ := by ring

lemma tensorMetric_inv_norm_bound {H : Matrix n n ℂ} (hHp : H.PosDef) {M : ℝ}
    (hM : 0 ≤ M) (hH : ‖H‖ ≤ M) (hI : ‖H⁻¹‖ ≤ M) : ‖(tensorMetric H)⁻¹‖ ≤ M^3 := by
  rw [tensorMetric_inv hHp]
  apply (tensor3_norm_le _ _ _).trans
  rw [Matrix.norm_transpose]
  calc
    _ ≤ M*M*M := mul_le_mul
      (mul_le_mul hH hI (norm_nonneg _) hM) hH (norm_nonneg _) (mul_nonneg hM hM)
    _ = _ := by ring

lemma tensorConnection_norm_le (G : Matrix n n ℂ) : ‖tensorConnection G‖ ≤ 3*‖G‖ := by
  have hone : ‖(1 : Matrix n n ℂ)‖ ≤ 1 := by
    apply matrix_norm_le_of_entries zero_le_one
    intro i j
    simp only [Matrix.one_apply]
    split_ifs <;> simp
  have h1 : ‖tensor3 (-G.transpose) 1 1‖ ≤ ‖G‖ := by
    apply (tensor3_norm_le _ _ _).trans
    simp only [norm_neg,Matrix.norm_transpose]
    nlinarith [norm_nonneg (1 : Matrix n n ℂ),norm_nonneg G,
      mul_le_mul_of_nonneg_left hone (norm_nonneg G),
      mul_le_mul_of_nonneg_left hone (mul_nonneg (norm_nonneg G) (norm_nonneg (1:Matrix n n ℂ)))]
  have h2 : ‖tensor3 1 G 1‖ ≤ ‖G‖ := by
    apply (tensor3_norm_le _ _ _).trans
    nlinarith [norm_nonneg (1 : Matrix n n ℂ),norm_nonneg G,
      mul_le_mul_of_nonneg_right hone (norm_nonneg G),
      mul_le_mul_of_nonneg_left hone (mul_nonneg (norm_nonneg (1:Matrix n n ℂ)) (norm_nonneg G))]
  have h3 : ‖tensor3 1 1 (-G.transpose)‖ ≤ ‖G‖ := by
    apply (tensor3_norm_le _ _ _).trans
    simp only [norm_neg,Matrix.norm_transpose]
    have ho : ‖(1 : Matrix n n ℂ)‖*‖(1 : Matrix n n ℂ)‖ ≤ 1 :=
      (mul_le_mul hone hone (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)
    simpa using mul_le_mul_of_nonneg_right ho (norm_nonneg G)
  exact (norm_add_le _ _).trans ((add_le_add ((norm_add_le _ _).trans
    (add_le_add h1 h2)) h3).trans_eq (by ring))

omit [DecidableEq n] in
lemma matrix_norm_mul_le (A B : Matrix n n ℂ) :
    ‖A*B‖ ≤ (Fintype.card n:ℝ)*‖A‖*‖B‖ := by
  exact matrix_norm_le_of_entries (by positivity)
    (entry_mul_bound (norm_nonneg A) (fun _ _ => norm_entry_le_entrywise_sup_norm A)
      (fun _ _ => norm_entry_le_entrywise_sup_norm B))

omit [DecidableEq n] in
lemma mulVec_norm_le (A : Matrix n n ℂ) (v : n → ℂ) :
    ‖A*ᵥ v‖ ≤ (Fintype.card n:ℝ)*‖A‖*‖v‖ := by
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro i
  calc
    _ ≤ ∑ j, ‖A i j*v j‖ := norm_sum_le _ _
    _ ≤ ∑ _j : n, ‖A‖*‖v‖ := Finset.sum_le_sum (fun j _ => by
      rw [norm_mul]
      exact mul_le_mul (norm_entry_le_entrywise_sup_norm A) (norm_le_pi_norm v j)
        (norm_nonneg _) (norm_nonneg _))
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]; ring

end MongeAmpere

end

end OAI
