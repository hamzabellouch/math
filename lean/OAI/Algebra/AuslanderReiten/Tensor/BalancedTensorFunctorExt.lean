import OAI.Algebra.AuslanderReiten.Tensor.BalancedTensorNativeEvaluation

namespace OAI

noncomputable section
open CategoryTheory
namespace ArExplicit.BalancedTensor
universe u
variable {k R S F : Type u} [Field k] [Ring R] [Ring S] [Algebra k R]
variable [AddCommGroup F] [Module k F] [Module Rᵐᵒᵖ F] [Module S F]
variable [SMulCommClass k S F] [SMulCommClass S Rᵐᵒᵖ F]
variable (M : ModuleCat.{u} R) (N : ModuleCat.{u} S)

theorem functorIso_ext
    (d e : (functor (k := k) (R := R) (S := S) (F := F)).obj M ≅ N)
    (h : ∀ (f : F) (m : M),
      d.hom.hom (letI := moduleCatBaseModule (k := k) (R := R) M; tmul f m) =
        e.hom.hom (letI := moduleCatBaseModule (k := k) (R := R) M; tmul f m)) : d = e := by
  apply Iso.ext
  apply ModuleCat.hom_ext
  let := moduleCatBaseModule (k := k) (R := R) M
  let := moduleCatBaseTower (k := k) (R := R) M
  apply leftHom_ext
  exact h

end ArExplicit.BalancedTensor

end

end OAI
