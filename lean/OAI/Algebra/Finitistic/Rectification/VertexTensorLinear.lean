import OAI.Algebra.Finitistic.Rectification.CornerPathTransport

namespace OAI
noncomputable section
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra
namespace LittleFinitistic.BimoduleVertex
universe u
variable (k B : Type u) [Field k] [Ring B] [Algebra k B]

instance linear (e : B) : (functor k B e).Linear k where
  map_smul := by
    intro M N f c
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    change algebraMap k (B ⊗[k] Bᵐᵒᵖ) c • (f.hom x.val) =
      restriction k B (algebraMap k Bᵐᵒᵖ c) • (f.hom x.val)
    rw [show restriction k B (algebraMap k Bᵐᵒᵖ c) =
      algebraMap k (B ⊗[k] Bᵐᵒᵖ) c from
      (Algebra.TensorProduct.includeRight : Bᵐᵒᵖ →ₐ[k] B ⊗[k] Bᵐᵒᵖ).commutes c]
end LittleFinitistic.BimoduleVertex

namespace LittleFinitistic.TensorComplex
universe u
variable {k B : Type u} [Field k] [Ring B] [Algebra k B]
variable (D : CochainComplex (ModuleCat.{u} Bᵐᵒᵖ) ℤ)
instance linear : (tensorFunctor (k := k) D).Linear k where
  map_smul := by
    intro M N f c
    apply HomologicalComplex.Hom.ext
    funext n
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    induction x using TensorProduct.inductionOn with
    | tmul m y =>
      change (c • f.hom m) ⊗ₜ[k] y = f.hom m ⊗ₜ[k]
        ((algebraMap k Bᵐᵒᵖ c) • (y : D.X n))
      exact TensorProduct.smul_tmul (R := k) c (f.hom m) (y : ScalarModule k B (D.X n))
    | add x y hx hy =>
      exact (map_add _ _ _).trans
        ((congrArg₂ (· + ·) hx hy).trans (map_add _ _ _).symm)
end LittleFinitistic.TensorComplex

end

end OAI
