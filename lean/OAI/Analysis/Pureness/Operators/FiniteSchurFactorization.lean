import OAI.Analysis.Pureness.Operators.FiniteGramSchur
import Mathlib.Analysis.InnerProductSpace.PiL2

namespace OAI
noncomputable section
namespace CuntzPureness
open CuntzComparison
open scoped TensorProduct InnerProductSpace
variable {E V ι : Type*} [Fintype ι]
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable [NormedAddCommGroup V] [InnerProductSpace ℂ V]

def finiteSchurFactorization (e : ι → E) (v w : ι → V) (T : E →L[ℂ] E) : E →L[ℂ] E :=
  (finiteGramDilation e v).adjoint.comp
    ((spatialTensorOp T (1 : V →L[ℂ] V)).comp (finiteGramDilation e w))

theorem finiteSchurFactorization_norm_le (e : ι → E) (he : Orthonormal ℂ e)
    (v w : ι → V) (hv : ∀ i, ‖v i‖ ≤ 1) (hw : ∀ i, ‖w i‖ ≤ 1)
    (T : E →L[ℂ] E) : ‖finiteSchurFactorization e v w T‖ ≤ ‖T‖ := by
  have hdv := finiteGramDilation_norm_le e he v hv
  have hdw := finiteGramDilation_norm_le e he w hw
  have ht : ‖spatialTensorOp T (1 : V →L[ℂ] V)‖ ≤ ‖T‖ := by
    apply (spatialTensorOp_norm_le _ _).trans
    exact (mul_le_mul_of_nonneg_left (ContinuousLinearMap.norm_id_le (𝕜 := ℂ) (E := V))
      (norm_nonneg T)).trans_eq (mul_one _)
  unfold finiteSchurFactorization
  apply (ContinuousLinearMap.opNorm_comp_le _ _).trans
  apply (mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _)).trans
  rw [LinearIsometryEquiv.norm_map]
  calc
    _ ≤ 1 * (‖T‖ * 1) := by gcongr
    _ = ‖T‖ := by ring

lemma finiteSchurFactorization_entry (e : ι → E) (he : Orthonormal ℂ e) (v w : ι → V)
    (T : E →L[ℂ] E) (i j : ι) :
    ⟪e i, finiteSchurFactorization e v w T (e j)⟫_ℂ =
      ⟪e i, T (e j)⟫_ℂ * ⟪v i, w j⟫_ℂ := by
  simp only [finiteSchurFactorization, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.adjoint_inner_right, finiteGramDilation_basis e he,
    spatialTensorOp_coe, TensorProduct.mapL_tmul, one_apply_eq_self,
    UniformSpace.Completion.inner_coe, TensorProduct.inner_tmul]

omit [CompleteSpace E] in
lemma operator_eq_of_orthonormalBasis_entries (e : OrthonormalBasis ι ℂ E)
    (S T : E →L[ℂ] E) (h : ∀ i j, ⟪e i, S (e j)⟫_ℂ = ⟪e i, T (e j)⟫_ℂ) : S = T := by
  have hb (j : ι) : S (e j) = T (e j) := by
    apply e.repr.injective
    ext i
    exact (e.repr_apply_apply _ i).trans ((h i j).trans (e.repr_apply_apply _ i).symm)
  apply ContinuousLinearMap.ext
  intro x
  conv_lhs => rw [← e.sum_repr' x]
  conv_rhs => rw [← e.sum_repr' x]
  simp only [map_sum, map_smul, hb]

theorem norm_le_of_schur_factorization (e : OrthonormalBasis ι ℂ E)
    (v w : ι → V) (hv : ∀ i, ‖v i‖ ≤ 1) (hw : ∀ i, ‖w i‖ ≤ 1)
    (S T : E →L[ℂ] E)
    (h : ∀ i j, ⟪e i, S (e j)⟫_ℂ = ⟪e i, T (e j)⟫_ℂ * ⟪v i, w j⟫_ℂ) :
    ‖S‖ ≤ ‖T‖ := by
  have heq : S = finiteSchurFactorization e v w T :=
    operator_eq_of_orthonormalBasis_entries e S _
      (fun i j => (h i j).trans (finiteSchurFactorization_entry e e.orthonormal v w T i j).symm)
  rw [heq]
  exact finiteSchurFactorization_norm_le e e.orthonormal v w hv hw T
end CuntzPureness

end

end OAI
