import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

namespace OAI
noncomputable section
open CategoryTheory
namespace LittleFinitistic.AdditiveSplitImage
universe u v
variable {C : Type*} [Category C]
variable {R : Type u} [Ring R]
variable (F : C ⥤ ModuleCat.{v} R)
variable {V M : C} (i : V ⟶ M) (p : M ⟶ V) (hip : i ≫ p = 𝟙 V)

def fixed : Submodule R (F.obj M) := ((F.map (p ≫ i)).hom - LinearMap.id).ker

@[simp] theorem mem_fixed (x : F.obj M) : x ∈ fixed F i p ↔ (F.map (p ≫ i)).hom x = x := by
  simp [fixed,sub_eq_zero]

def forward : F.obj V →ₗ[R] fixed F i p :=
  (F.map i).hom.codRestrict _ (by
    intro x
    rw [mem_fixed]
    have he : F.map i ≫ F.map (p ≫ i) = F.map i := by
      rw [← F.map_comp,← Category.assoc,hip,Category.id_comp]
    exact congrArg (fun a : F.obj V ⟶ F.obj M => a.hom x) he)

def inverse : fixed F i p →ₗ[R] F.obj V :=
  (F.map p).hom.comp (fixed F i p).subtype

/-- Any additive module-valued functor preserves the actual image of a split idempotent. -/
def equiv : F.obj V ≃ₗ[R] fixed F i p where
  __ := forward F i p hip
  invFun := inverse F i p
  left_inv x := by
    have he : F.map i ≫ F.map p = 𝟙 (F.obj V) := by rw [← F.map_comp,hip,F.map_id]
    exact congrArg (fun a : F.obj V ⟶ F.obj V => a.hom x) he
  right_inv x := by
    apply Subtype.ext
    change (F.map i).hom ((F.map p).hom x.val) = x.val
    rw [show (F.map i).hom ((F.map p).hom x.val) = (F.map (p ≫ i)).hom x.val from
      congrArg (fun a : F.obj M ⟶ F.obj M => a.hom x.val) (F.map_comp p i).symm]
    exact (mem_fixed F i p x.val).1 x.property

@[simp] theorem equiv_apply_val (x : F.obj V) : (equiv F i p hip x).val = (F.map i).hom x := rfl
@[simp] theorem equiv_symm_apply (x : fixed F i p) : (equiv F i p hip).symm x = (F.map p).hom x.val := rfl
end LittleFinitistic.AdditiveSplitImage

end

end OAI
