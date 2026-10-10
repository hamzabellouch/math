import Mathlib.LinearAlgebra.Quotient.Basic

namespace OAI

namespace ArExplicit

universe u

variable {R M N M' N' : Type u} [Ring R]
variable [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
variable [AddCommGroup M'] [Module R M'] [AddCommGroup N'] [Module R N']

def cokernelLinearCongr (f : M →ₗ[R] N) (g : M' →ₗ[R] N')
    (a : M ≃ₗ[R] M') (b : N ≃ₗ[R] N') (h : b.toLinearMap.comp f = g.comp a.toLinearMap) :
    (N ⧸ LinearMap.range f) ≃ₗ[R] (N' ⧸ LinearMap.range g) :=
  Submodule.Quotient.equiv _ _ b (by
    ext y
    constructor
    · rintro ⟨x, ⟨z, rfl⟩, rfl⟩
      exact ⟨a z, (DFunLike.congr_fun h z).symm⟩
    · rintro ⟨z, rfl⟩
      refine ⟨f (a.symm z), ⟨a.symm z, rfl⟩, ?_⟩
      change b.toLinearMap.comp f (a.symm z) = g z
      rw [h]
      simp)

@[simp]
theorem cokernelLinearCongr_mk (f : M →ₗ[R] N) (g : M' →ₗ[R] N')
    (a : M ≃ₗ[R] M') (b : N ≃ₗ[R] N') (h : b.toLinearMap.comp f = g.comp a.toLinearMap)
    (x : N) :
    cokernelLinearCongr f g a b h (Submodule.Quotient.mk x) = Submodule.Quotient.mk (b x) := rfl

end ArExplicit

end OAI
