import OAI.Algebra.AuslanderReiten.Modules.TInductionHomology
import Mathlib.Algebra.Category.ModuleCat.Algebra
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Linear

namespace OAI

noncomputable section
open CategoryTheory
open scoped ModuleCat
namespace ArExplicit.Resolution
universe u
variable {k : Type u} [Field k] (q : k)
local notation "T" => ArExplicit.T k q
local notation "S" => ModuleCat.of T (Simple q)

def tSimpleScalarEnd : k →ₗ[k] (S ⟶ S) :=
  LinearMap.toSpanSingleton k (S ⟶ S) (𝟙 S)

theorem tSimpleEnd_eq_scalar (hq1 : 1 + q ≠ 0) (f : S ⟶ S) :
    f = tSimpleScalarEnd q (simpleCoordinate q (f (generator q))) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change f.hom x = simpleCoordinate q (f.hom (generator q)) • x
  rw [simple_expand q hq1 x, LinearMap.map_smul_of_tower]
  rw [simple_expand q hq1 (f.hom (generator q)), smul_smul, smul_smul, mul_comm]
  simp

theorem tSimpleScalarEnd_bijective (hq1 : 1 + q ≠ 0) :
    Function.Bijective (tSimpleScalarEnd q) := by
  constructor
  · intro a b hab
    have hh := congrArg (fun f : S ⟶ S => simpleCoordinate q (f (generator q))) hab
    change simpleCoordinate q (a • generator q) = simpleCoordinate q (b • generator q) at hh
    simpa using hh
  · intro f
    exact ⟨simpleCoordinate q (f (generator q)), (tSimpleEnd_eq_scalar q hq1 f).symm⟩

def tSimpleEndScalarEquiv (hq1 : 1 + q ≠ 0) : k ≃ₗ[k] (S ⟶ S) :=
  LinearEquiv.ofBijective (tSimpleScalarEnd q) (tSimpleScalarEnd_bijective q hq1)

def tSimpleExtZeroEquiv (hq1 : 1 + q ≠ 0) : k ≃ₗ[k] Abelian.Ext S S 0 where
  toEquiv := (tSimpleEndScalarEquiv q hq1).toEquiv.trans Abelian.Ext.homEquiv₀.symm
  map_add' a b := by
    change Abelian.Ext.mk₀ (tSimpleScalarEnd q (a + b)) =
      Abelian.Ext.mk₀ (tSimpleScalarEnd q a) + Abelian.Ext.mk₀ (tSimpleScalarEnd q b)
    rw [map_add, Abelian.Ext.mk₀_add]
  map_smul' a b := by
    change Abelian.Ext.mk₀ (tSimpleScalarEnd q (a * b)) = a • Abelian.Ext.mk₀ (tSimpleScalarEnd q b)
    rw [← Abelian.Ext.mk₀_smul]
    congr 1
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change (a * b) • x = (algebraMap k T a) • (b • x)
    rw [IsScalarTower.algebraMap_smul]
    exact mul_smul a b x

@[simp] theorem tSimpleExtZeroEquiv_one (hq1 : 1 + q ≠ 0) :
    tSimpleExtZeroEquiv q hq1 1 = Abelian.Ext.mk₀ (𝟙 S) := by
  change Abelian.Ext.mk₀ (tSimpleScalarEnd q 1) = _
  congr 1
  exact one_smul k (𝟙 S)

end ArExplicit.Resolution

end

end OAI
