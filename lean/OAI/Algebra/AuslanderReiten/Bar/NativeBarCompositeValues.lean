import OAI.Algebra.AuslanderReiten.Bar.NativeBarFreeEndpoint

namespace OAI

noncomputable section
namespace ArExplicit.BarBalanced
open CategoryTheory
universe u
variable (k R M : Type u) [Field k] [Ring R] [Algebra k R] [CharP k 2]
variable [AddCommGroup M] [Module R M] [Module k M] [IsScalarTower k R M]

theorem nativeFreeEndpoint_definition (e : M ≃ₗ[k] k) :
    nativeFreeEndpoint k R M e = (nativeComplexIso k R M).hom.f 0 ≫
      (ModuleBar.freeCoordinate k R M e).toModuleIso.hom := rfl

private theorem valueOfMapEq {R : Type*} [Ring R] {X Y : ModuleCat R}
    {f g : X ⟶ Y} (h : f=g) {x : X} {y : Y} (hv : g x=y) : f x=y := by
  rw [h, hv]

theorem nativeComposite_tensor (e : M ≃ₗ[k] k) (a b : R) (m : M) :
    type_of% (valueOfMapEq (nativeFreeEndpoint_definition k R M e).symm
      (nativeFreeEndpoint_tensor k R M e a b m)) :=
  valueOfMapEq (nativeFreeEndpoint_definition k R M e).symm
    (nativeFreeEndpoint_tensor k R M e a b m)

end ArExplicit.BarBalanced

end

end OAI
