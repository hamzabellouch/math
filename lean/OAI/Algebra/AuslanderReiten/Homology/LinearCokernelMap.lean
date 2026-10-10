import Mathlib.LinearAlgebra.Isomorphisms

namespace OAI

noncomputable section
namespace ArExplicit.LinearCokernel
variable {R : Type*} [Ring R]
variable {L M L' M' L'' M'' : Type*}
variable [AddCommGroup L] [Module R L] [AddCommGroup M] [Module R M]
variable [AddCommGroup L'] [Module R L'] [AddCommGroup M'] [Module R M']
variable [AddCommGroup L''] [Module R L''] [AddCommGroup M''] [Module R M'']

def map (d : L →ₗ[R] M) (d' : L' →ₗ[R] M')
    (a : L →ₗ[R] L') (b : M →ₗ[R] M') (h : b.comp d = d'.comp a) :
    (M ⧸ LinearMap.range d) →ₗ[R] (M' ⧸ LinearMap.range d') :=
  (LinearMap.range d).liftQ ((LinearMap.range d').mkQ.comp b) (by
    rintro z ⟨x,rfl⟩
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    exact ⟨a x, (DFunLike.congr_fun h x).symm⟩)

@[simp] theorem map_mk (d : L →ₗ[R] M) (d' : L' →ₗ[R] M')
    (a : L →ₗ[R] L') (b : M →ₗ[R] M') (h : b.comp d = d'.comp a) (x : M) :
    map d d' a b h (Submodule.Quotient.mk x) = Submodule.Quotient.mk (b x) := rfl

private theorem inverse_square (d : L →ₗ[R] M) (d' : L' →ₗ[R] M')
    (a : L ≃ₗ[R] L') (b : M ≃ₗ[R] M') (h : b.toLinearMap.comp d = d'.comp a.toLinearMap) :
    b.symm.toLinearMap.comp d' = d.comp a.symm.toLinearMap := by
  ext x
  apply b.injective
  simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
    using (DFunLike.congr_fun h (a.symm x)).symm

def equiv (d : L →ₗ[R] M) (d' : L' →ₗ[R] M')
    (a : L ≃ₗ[R] L') (b : M ≃ₗ[R] M') (h : b.toLinearMap.comp d = d'.comp a.toLinearMap) :
    (M ⧸ LinearMap.range d) ≃ₗ[R] (M' ⧸ LinearMap.range d') where
  __ := map d d' a.toLinearMap b.toLinearMap h
  invFun := map d' d a.symm.toLinearMap b.symm.toLinearMap (inverse_square d d' a b h)
  left_inv x := by
    obtain ⟨x,rfl⟩ := (LinearMap.range d).mkQ_surjective x
    change Submodule.Quotient.mk (b.symm (b x)) = Submodule.Quotient.mk x
    rw [LinearEquiv.symm_apply_apply]
  right_inv x := by
    obtain ⟨x,rfl⟩ := (LinearMap.range d').mkQ_surjective x
    change Submodule.Quotient.mk (b (b.symm x)) = Submodule.Quotient.mk x
    rw [LinearEquiv.apply_symm_apply]

@[simp] theorem equiv_mk (d : L →ₗ[R] M) (d' : L' →ₗ[R] M')
    (a : L ≃ₗ[R] L') (b : M ≃ₗ[R] M') (h : b.toLinearMap.comp d = d'.comp a.toLinearMap) (x : M) :
    equiv d d' a b h (Submodule.Quotient.mk x) = Submodule.Quotient.mk (b x) := rfl

end ArExplicit.LinearCokernel

end

end OAI
