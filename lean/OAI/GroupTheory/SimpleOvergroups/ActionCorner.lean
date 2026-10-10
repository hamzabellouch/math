import Mathlib
import OAI.GroupTheory.SimpleOvergroups.ActionMonoid

namespace OAI


noncomputable section
namespace SimpleFInftyOvergroups.RingAssembly
open SourceActionMonoid
open scoped Classical
variable {V Y R : Type*} [Group V] [MulAction V Y] [Ring R]

local instance actionCornerMonoidWithZero : MonoidWithZero (M V Y) where
  __ := (inferInstance : Monoid (M V Y))
  zero := omega
  zero_mul := omega_mul
  mul_zero := mul_omega

variable (δ : M V Y →*₀ R)

def actionUnits : V →* Rˣ := (δ.toMonoidHom.comp groupMap).toHomUnits

theorem actionUnits_val (w : V) : (actionUnits δ w).val=δ (groupMap w) := rfl

theorem actionUnits_injective (hδ : Function.Injective δ) : Function.Injective (actionUnits δ) := by
  intro w v hwv
  apply groupMap_injective (Z:=Y)
  exact hδ (congrArg Units.val hwv)

theorem corner_TS (y z : Y) : δ (delete y) * δ (prepend z)=if y=z then 1 else 0 := by
  rw [←map_mul]
  by_cases hyz : y=z
  · subst z
    rw [ite_eq_left rfl,delete_prefix,map_one]
  · rw [ite_eq_right hyz,delete_prefix_ne y z hyz]
    exact map_zero δ

theorem corner_ρS (w : V) (y : Y) : (actionUnits δ w).val * δ (prepend y)=δ (prepend (w • y)) := by
  rw [actionUnits_val,←map_mul,group_prefix]

theorem corner_Tρ (w : V) (y : Y) : δ (delete y) * (actionUnits δ w).val=δ (delete (w⁻¹ • y)) := by
  rw [actionUnits_val,←map_mul,delete_group]

end SimpleFInftyOvergroups.RingAssembly
end

end OAI
