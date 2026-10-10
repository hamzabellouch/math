import Mathlib

namespace OAI

section
namespace ElementaryPositivity.FiniteLog
open WithConv
variable {R C A B : Type*} [CommSemiring R] [AddCommMonoid C] [Module R C]
  [Coalgebra R C] [Semiring A] [Semiring B] [Algebra R A] [Algebra R B]

noncomputable def convPost (φ : A →ₐ[R] B) : WithConv (C →ₗ[R] A) →ₐ[R] WithConv (C →ₗ[R] B) where
  toFun f := toConv (φ.toLinearMap.comp f.ofConv)
  map_zero' := by apply WithConv.ofConv_injective; ext x; exact φ.map_zero
  map_add' f g := by apply WithConv.ofConv_injective; ext x; exact φ.map_add _ _
  map_one' := by
    apply WithConv.ofConv_injective
    ext x
    exact φ.commutes _
  map_mul' f g := WithConv.ofConv_injective (LinearMap.algHom_comp_convMul_distrib φ f g)
  commutes' r := by
    apply WithConv.ofConv_injective
    ext x
    change φ (r • algebraMap R A (Coalgebra.counit (R := R) x))=
      r • algebraMap R B (Coalgebra.counit (R := R) x)
    rw [map_smul,φ.commutes]

lemma convPost_apply (φ : A →ₐ[R] B) (f : WithConv (C →ₗ[R] A)) (x : C) :
    ((convPost φ) f).ofConv x=φ (f.ofConv x) := rfl

end ElementaryPositivity.FiniteLog

end

end OAI
