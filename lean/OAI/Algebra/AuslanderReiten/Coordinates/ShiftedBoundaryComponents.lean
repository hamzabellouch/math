import Mathlib.CategoryTheory.Shift.ShiftedHom

namespace OAI

noncomputable section
namespace ArExplicit
open CategoryTheory
universe u v
variable {C : Type u} [Category.{v} C] [HasShift C ℤ]
variable {X U V W Z : C}

theorem shiftedComp_pre (a : ℤ) (v : X ⟶ U⟦a⟧) (p : U ⟶ V)
    (s : V ⟶ W⟦(1 : ℤ)⟧) :
    ShiftedHom.comp v (p ≫ s) (add_comm 1 a) =
      ShiftedHom.comp (v ≫ p⟦a⟧') s (add_comm 1 a) := by
  simp only [ShiftedHom.comp, Functor.map_comp, Category.assoc]

theorem shiftedComp_post (a : ℤ) (v : X ⟶ U⟦a⟧)
    (s : U ⟶ W⟦(1 : ℤ)⟧) (c : W ⟶ Z) :
    ShiftedHom.comp v (s ≫ c⟦(1 : ℤ)⟧') (add_comm 1 a) =
      ShiftedHom.comp v s (add_comm 1 a) ≫ c⟦a+1⟧' := by
  have h := ShiftedHom.comp_assoc v s (ShiftedHom.mk₀ (0 : ℤ) rfl c)
    (add_comm 1 a) (by omega : (0 : ℤ)+1=1) (by omega : (0 : ℤ)+1+a=a+1)
  simpa only [ShiftedHom.comp_mk₀] using h.symm

theorem shiftedComp_prepost (a : ℤ) (v : X ⟶ U⟦a⟧) (p : U ⟶ V)
    (s : V ⟶ W⟦(1 : ℤ)⟧) (c : W ⟶ Z) :
    ShiftedHom.comp v ((p ≫ s) ≫ c⟦(1 : ℤ)⟧') (add_comm 1 a) =
      ShiftedHom.comp (v ≫ p⟦a⟧') s (add_comm 1 a) ≫ c⟦a+1⟧' := by
  rw [shiftedComp_post, shiftedComp_pre]

variable [Preadditive C] [∀ n : ℤ, (CategoryTheory.shiftFunctor C n).Additive]

theorem shiftedComp_row (a : ℤ) (v : X ⟶ U⟦a⟧) (p r : U ⟶ V)
    (s : V ⟶ W⟦(1 : ℤ)⟧) (c d : W ⟶ Z) :
    ShiftedHom.comp v (((p ≫ s) ≫ c⟦(1 : ℤ)⟧') + ((r ≫ s) ≫ d⟦(1 : ℤ)⟧'))
        (add_comm 1 a) =
      (ShiftedHom.comp (v ≫ p⟦a⟧') s (add_comm 1 a) ≫ c⟦a+1⟧') +
      (ShiftedHom.comp (v ≫ r⟦a⟧') s (add_comm 1 a) ≫ d⟦a+1⟧') := by
  rw [ShiftedHom.comp_add, shiftedComp_prepost, shiftedComp_prepost]

end ArExplicit

end

end OAI
