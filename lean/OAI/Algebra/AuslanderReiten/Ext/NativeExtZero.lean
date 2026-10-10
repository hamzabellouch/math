import OAI.Algebra.AuslanderReiten.Ext.ExtIsoCongr
import Mathlib.Algebra.Category.ModuleCat.Algebra

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Abelian
open scoped ModuleCat.Algebra
namespace ArExplicit
universe u
variable {k R : Type u} [Field k] [Ring R] [Algebra k R]
variable (M N : ModuleCat.{u} R) [Module k N] [IsScalarTower k R N]

def nativeExtMkZero : (M →ₗ[R] N) →ₗ[k] Ext M N 0 where
  toFun f := Ext.mk₀ (ModuleCat.ofHom f)
  map_add' f g := by rw [ModuleCat.ofHom_add, Ext.mk₀_add]
  map_smul' c f := by
    rw [← Ext.mk₀_smul]
    congr 1
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change c • f x = (algebraMap k R c) • f x
    exact (IsScalarTower.algebraMap_smul R c (f x)).symm

def nativeExtZeroEquiv : (M →ₗ[R] N) ≃ₗ[k] Ext M N 0 :=
  LinearEquiv.ofBijective (nativeExtMkZero M N)
    ((Ext.mk₀_bijective M N).comp
      ⟨fun _f _g h => ModuleCat.hom_ext_iff.mp h, fun f => ⟨f.hom,rfl⟩⟩)

@[simp]
theorem nativeExtZeroEquiv_apply (f : M →ₗ[R] N) :
    nativeExtZeroEquiv (k := k) M N f = Ext.mk₀ (ModuleCat.ofHom f) := rfl

end ArExplicit

end

end OAI
