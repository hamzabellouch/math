import OAI.Probability.SignedSweeps.TensorCommutant

namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct Classical
open Module
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]

lemma norm_positiveRoot_square (T : E →ₗ[ℂ] E) (x : E) :
    ‖positiveRoot (positiveSquare T) (adjoint_mul_positive T) x‖ = ‖T x‖ := by
  let P := positiveRoot (positiveSquare T) (adjoint_mul_positive T)
  have hp := positiveRoot_positive (positiveSquare T) (adjoint_mul_positive T)
  have he : inner ℂ (P x) (P x) = inner ℂ (T x) (T x) := by
    rw [hp.isSymmetric x (P x)]
    change inner ℂ x ((P * P) x) = _
    rw [positiveRoot_square]
    exact LinearMap.adjoint_inner_right T x (T x)
  have hr := congrArg Complex.re he
  simp only [inner_self_eq_norm_sq_to_K, RCLike.ofReal_eq_complex_ofReal,
    ← Complex.ofReal_pow, Complex.ofReal_re] at hr
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hr

def rangeNormIsometry (A B : E →ₗ[ℂ] E) (h : ∀ x, ‖A x‖ = ‖B x‖) :
    A.range →ₗᵢ[ℂ] E := by
  have hk : A.ker ≤ B.ker := by
    intro x hx
    rw [LinearMap.mem_ker] at hx ⊢
    exact norm_eq_zero.mp (by rw [← h, hx, norm_zero])
  let L := (A.ker.liftQ B hk).comp A.quotKerEquivRange.symm.toLinearMap
  have hL (x : E) : L ⟨A x, LinearMap.mem_range_self A x⟩ = B x := by
    have hx : A.quotKerEquivRange (Submodule.Quotient.mk x) =
        (⟨A x, LinearMap.mem_range_self A x⟩ : A.range) := by
      exact Subtype.ext (LinearMap.quotKerEquivRange_apply_mk A x)
    simp only [L, LinearMap.comp_apply, LinearEquiv.coe_coe, ← hx,
      LinearEquiv.symm_apply_apply, Submodule.liftQ_apply]
  refine ⟨L, ?_⟩
  rintro ⟨_, x, rfl⟩
  exact (congrArg norm (hL x)).trans (h x).symm

omit [FiniteDimensional ℂ E] in
lemma rangeNormIsometry_apply (A B : E →ₗ[ℂ] E) (h : ∀ x, ‖A x‖ = ‖B x‖) (x : E) :
    rangeNormIsometry A B h ⟨A x, LinearMap.mem_range_self A x⟩ = B x := by
  dsimp only [rangeNormIsometry, LinearIsometry.coe_mk, LinearMap.comp_apply,
    LinearEquiv.coe_coe]
  have hx : A.quotKerEquivRange (Submodule.Quotient.mk x) =
      (⟨A x, LinearMap.mem_range_self A x⟩ : A.range) :=
    Subtype.ext (LinearMap.quotKerEquivRange_apply_mk A x)
  rw [← hx, LinearEquiv.symm_apply_apply, Submodule.liftQ_apply]

theorem exists_unitary_positive_factor (T : E →ₗ[ℂ] E) :
    ∃ U : E ≃ₗᵢ[ℂ] E, ∃ P : E →ₗ[ℂ] E, P.IsPositive ∧
      T = U.toLinearEquiv.toLinearMap * P := by
  let P := positiveRoot (positiveSquare T) (adjoint_mul_positive T)
  let L := rangeNormIsometry P T (norm_positiveRoot_square T)
  refine ⟨L.extend.toLinearIsometryEquiv rfl, P,
    positiveRoot_positive _ _, ?_⟩
  ext x
  change T x = L.extend (P x)
  rw [LinearIsometry.extend_apply L (⟨P x, LinearMap.mem_range_self P x⟩ : P.range)]
  exact (rangeNormIsometry_apply P T _ x).symm

end SignedSweeps
end

end OAI
