import OAI.Analysis.Pureness.Tensor.SpatialVectorSlice
import Mathlib.Analysis.InnerProductSpace.Orthonormal

namespace OAI
noncomputable section
namespace CuntzPureness
open CuntzComparison
open scoped TensorProduct InnerProductSpace
variable {E V ι : Type*} [Fintype ι]
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable [NormedAddCommGroup V] [InnerProductSpace ℂ V]

def finiteGramDilation (e : ι → E) (v : ι → V) : E →L[ℂ] SpatialHilbert E V :=
  ∑ i, InnerProductSpace.rankOne ℂ (spatialRightVector (v i) (e i)) (e i)

lemma finiteGramDilation_apply (e : ι → E) (v : ι → V) (x : E) :
    finiteGramDilation e v x = ∑ i, ⟪e i, x⟫_ℂ •
      ((e i ⊗ₜ[ℂ] v i : E ⊗[ℂ] V) : SpatialHilbert E V) := by
  simp only [finiteGramDilation, sum_apply, InnerProductSpace.rankOne_apply]
  rfl

lemma finiteGramDilation_basis (e : ι → E) (he : Orthonormal ℂ e) (v : ι → V) (j : ι) :
    finiteGramDilation e v (e j) = (e j ⊗ₜ[ℂ] v j : E ⊗[ℂ] V) := by
  classical
  rw [finiteGramDilation_apply]
  simp [orthonormal_iff_ite.mp he]

lemma finiteGramDilation_norm_sq (e : ι → E) (he : Orthonormal ℂ e) (v : ι → V) (x : E) :
    ‖finiteGramDilation e v x‖ ^ 2 = ∑ i, ‖⟪e i, x⟫_ℂ‖ ^ 2 * ‖v i‖ ^ 2 := by
  classical
  rw [@norm_sq_eq_re_inner ℂ, finiteGramDilation_apply]
  simp only [sum_inner, inner_sum, inner_smul_left, inner_smul_right,
    UniformSpace.Completion.inner_coe, TensorProduct.inner_tmul, orthonormal_iff_ite.mp he]
  simp only [ite_mul, mul_ite, mul_zero, zero_mul, Finset.sum_ite_eq', Finset.mem_univ,
    ite_true]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [← mul_assoc, RCLike.mul_conj, one_mul, inner_self_eq_norm_sq_to_K]
  norm_cast

theorem finiteGramDilation_norm_le (e : ι → E) (he : Orthonormal ℂ e)
    (v : ι → V) (hv : ∀ i, ‖v i‖ ≤ 1) : ‖finiteGramDilation e v‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  have hn : ‖finiteGramDilation e v x‖ ^ 2 ≤ ‖x‖ ^ 2 := by
    rw [finiteGramDilation_norm_sq e he]
    apply le_trans _ (he.sum_inner_products_le x (s := Finset.univ))
    apply Finset.sum_le_sum
    intro i _
    have hi : ‖v i‖ ^ 2 ≤ 1 := by nlinarith [hv i, norm_nonneg (v i)]
    nlinarith [sq_nonneg ‖⟪e i, x⟫_ℂ‖]
  rw [one_mul]
  nlinarith [norm_nonneg (finiteGramDilation e v x), norm_nonneg x]

variable [CompleteSpace E]

def finiteGramSchur (e : ι → E) (v : ι → V) (T : E →L[ℂ] E) : E →L[ℂ] E :=
  (finiteGramDilation e v).adjoint.comp
    ((spatialTensorOp T (1 : V →L[ℂ] V)).comp (finiteGramDilation e v))

theorem finiteGramSchur_norm_le (e : ι → E) (he : Orthonormal ℂ e)
    (v : ι → V) (hv : ∀ i, ‖v i‖ ≤ 1) (T : E →L[ℂ] E) :
    ‖finiteGramSchur e v T‖ ≤ ‖T‖ := by
  have hd := finiteGramDilation_norm_le e he v hv
  have ht : ‖spatialTensorOp T (1 : V →L[ℂ] V)‖ ≤ ‖T‖ := by
    apply (spatialTensorOp_norm_le _ _).trans
    exact (mul_le_mul_of_nonneg_left (ContinuousLinearMap.norm_id_le (𝕜 := ℂ) (E := V))
      (norm_nonneg T)).trans_eq (mul_one _)
  unfold finiteGramSchur
  apply (ContinuousLinearMap.opNorm_comp_le _ _).trans
  apply (mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _)).trans
  rw [LinearIsometryEquiv.norm_map]
  calc
    _ ≤ 1 * (‖T‖ * 1) := by gcongr
    _ = ‖T‖ := by ring

lemma finiteGramSchur_entry (e : ι → E) (he : Orthonormal ℂ e) (v : ι → V)
    (T : E →L[ℂ] E) (i j : ι) :
    ⟪e i, finiteGramSchur e v T (e j)⟫_ℂ = ⟪e i, T (e j)⟫_ℂ * ⟪v i, v j⟫_ℂ := by
  simp only [finiteGramSchur, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.adjoint_inner_right, finiteGramDilation_basis e he,
    spatialTensorOp_coe, TensorProduct.mapL_tmul, one_apply_eq_self,
    UniformSpace.Completion.inner_coe, TensorProduct.inner_tmul]
end CuntzPureness

end

end OAI
