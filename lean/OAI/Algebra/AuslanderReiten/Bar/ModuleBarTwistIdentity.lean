import OAI.Algebra.AuslanderReiten.Bar.ModuleBarTwistExtAction
import OAI.Algebra.AuslanderReiten.Resolutions.ResolutionExtIdentity

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Abelian
namespace ArExplicit.ModuleBar
universe u
variable (k R M : Type u) [Field k] [Ring R] [Algebra k R]
  [AddCommGroup M] [Module R M] [Module k M] [IsScalarTower k R M] [CharP k 2]
variable [HasDerivedCategory (ModuleCat.{u} R)]
variable (h : R ≃ₐ[k] R) (e : M ≃ₗ[k] M)
variable (he : ∀ a m, e (a • m) = h a • e m)

omit [HasDerivedCategory (ModuleCat.{u} R)] in
theorem transportedCochain_augmentation :
    transportedCochain k R M h e he 0 ((resolution k R M).π.f 0) =
      (resolution k R M).π.f 0 := by
  change transportedCochain k R M h e he 0 ((augmentation k R M).f 0) =
      (augmentation k R M).f 0
  rw [augmentation_zero]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change e.symm (boundary k R M 0 (transport k R M h e 1 x)) = boundary k R M 0 x
  exact (congrArg e.symm (transport_boundary k R M h e he 0 x).symm).trans
    (e.symm_apply_apply (boundary k R M 0 x))

theorem twistExtAction_identity :
    twistExtAction k R M h e he 0 (Ext.mk₀ (𝟙 (moduleObject k R M 0))) =
      Ext.mk₀ (𝟙 (moduleObject k R M 0)) := by
  change twistExtAction k R M h e he 0 (Ext.mk₀ (𝟙 (ModuleCat.of R M))) =
    Ext.mk₀ (𝟙 (ModuleCat.of R M))
  let P := resolution k R M
  let f : P.complex.X 0 ⟶ ModuleCat.of R M := P.π.f 0
  have hf : P.complex.d 1 0 ≫ f = 0 := P.complex_d_comp_π_f_zero
  have ha : P.extMk f 1 rfl hf = Ext.mk₀ (𝟙 (ModuleCat.of R M)) :=
    ResolutionProducts.extMk_augmentation P
  have hz : twistExtAction k R M h e he 0 (P.extMk f 1 rfl hf) = P.extMk f 1 rfl hf := by
    rw [twistExtAction_extMk_transported]
    congr 1
    exact transportedCochain_augmentation k R M h e he
  exact ((congrArg (twistExtAction k R M h e he 0) ha.symm).trans hz).trans ha

end ArExplicit.ModuleBar

end

end OAI
