import Mathlib
import OAI.GroupTheory.SimpleAmenable.Simplicial.PolygonMonoidalData

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section PolygonPositionalMonoidal

open Classical CategoryTheory
open scoped MonoidalCategory
namespace PolygonObject
variable {a : ℕ}

theorem positional_comp {U V W : PolygonObject a} {f : U ⟶ V} {g : V ⟶ W}
    (hf : Positional f) (hg : Positional g) : Positional (f≫g) :=
  (positionalSubgroupoid a).mul hf hg

theorem positional_inv {U V : PolygonObject a} {f : U ⟶ V}
    (hf : Positional f) : Positional (CategoryTheory.inv f) := by
  rw [←Groupoid.inv_eq_inv]
  exact (positionalSubgroupoid a).inv hf

theorem sumArrow_positional {U V W Z : PolygonObject a} {f : U ⟶ W} {g : V ⟶ Z}
    (hf : Positional f) (hg : Positional g) : Positional (sumArrow f g) := by
  intro x
  obtain ⟨y,rfl⟩ := (sumPointEquiv U V).surjective x
  cases y with
  | inl y => simpa only [sumArrow_inl,sumPointEquiv_inl] using hf y
  | inr y => simpa only [sumArrow_inr,sumPointEquiv_inr] using hg y

theorem sumSwap_positional (U V : PolygonObject a) : Positional (sumSwap U V) := by
  intro x
  obtain ⟨y,rfl⟩ := (sumPointEquiv U V).surjective x
  cases y <;> simp only [sumSwap_apply,sumSwapEquiv_inl,sumSwapEquiv_inr,
    sumPointEquiv_inl,sumPointEquiv_inr]

theorem sumAssoc_positional (U V W : PolygonObject a) : Positional (sumAssoc U V W) := by
  intro x
  obtain ⟨y,rfl⟩ := (sumPointEquiv (sum U V) W).surjective x
  cases y with
  | inl y =>
    obtain ⟨z,rfl⟩ := (sumPointEquiv U V).surjective y
    cases z <;> simp only [sumAssoc_apply,sumAssocEquiv_left,sumAssocEquiv_mid,
      sumPointEquiv_inl,sumPointEquiv_inr]
  | inr y => simp only [sumAssoc_apply,sumAssocEquiv_right,sumPointEquiv_inr]

theorem leftUnit_positional (U : PolygonObject a) : Positional (leftUnit U) := by
  intro x
  obtain ⟨y,rfl⟩ := (sumPointEquiv empty U).surjective x
  cases y with
  | inl y => exact isEmptyElim y
  | inr y => simp only [leftUnit_apply,leftUnitEquiv_apply,sumPointEquiv_inr]

theorem rightUnit_positional (U : PolygonObject a) : Positional (rightUnit U) := by
  intro x
  obtain ⟨y,rfl⟩ := (sumPointEquiv U empty).surjective x
  cases y with
  | inl y => simp only [rightUnit_apply,rightUnitEquiv_apply,sumPointEquiv_inl]
  | inr y => exact isEmptyElim y

def positionalProperty (a : ℕ) : MorphismProperty (PolygonObject a) :=
  fun _ _ f => Positional f

instance positionalProperty_multiplicative : (positionalProperty a).IsMultiplicative where
  id_mem := identity_positional
  comp_mem _ _ := positional_comp

instance positionalProperty_monoidal : (positionalProperty a).IsMonoidalStable where
  whiskerLeft U _ _ _ hf := sumArrow_positional (identity_positional U) hf
  whiskerRight _ hf V := sumArrow_positional hf (identity_positional V)
  associator_hom_mem := sumAssoc_positional
  associator_inv_mem U V W := positional_inv (sumAssoc_positional U V W)
  leftUnitor_hom_mem := leftUnit_positional
  leftUnitor_inv_mem U := positional_inv (leftUnit_positional U)
  rightUnitor_hom_mem := rightUnit_positional
  rightUnitor_inv_mem U := positional_inv (rightUnit_positional U)

instance positionalProperty_braided : (positionalProperty a).IsStableUnderBraiding where
  braiding_hom_mem := sumSwap_positional
  braiding_inv_mem U V := positional_inv (sumSwap_positional U V)

abbrev PositionalCategory (a : ℕ) := WideSubcategory (positionalProperty a)

end PolygonObject
end PolygonPositionalMonoidal

end SimpleAmenable
end
end

end OAI
