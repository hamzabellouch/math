import Mathlib.Algebra.Category.ModuleCat.Ext.HasExt
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Linear

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Abelian
namespace ArExplicit
universe u v
variable {k : Type u} [CommRing k]
variable {C : Type v} [Category.{u} C] [Abelian C] [HasExt.{u} C] [Linear k C]
variable {X X' Y Y' : C}

def extSourceIso (e : X ≅ X') (Y : C) (n : ℕ) : Ext X Y n ≃ₗ[k] Ext X' Y n where
  toFun x := (Ext.mk₀ e.inv).comp x (zero_add n)
  invFun x := (Ext.mk₀ e.hom).comp x (zero_add n)
  left_inv x := by simp
  right_inv x := by simp
  map_add' x y := by simp
  map_smul' c x := by simp

def extTargetIso (X : C) (e : Y ≅ Y') (n : ℕ) : Ext X Y n ≃ₗ[k] Ext X Y' n where
  toFun x := x.comp (Ext.mk₀ e.hom) (add_zero n)
  invFun x := x.comp (Ext.mk₀ e.inv) (add_zero n)
  left_inv x := by simp
  right_inv x := by simp
  map_add' x y := by simp
  map_smul' c x := by simp

def selfExtIso (e : X ≅ Y) (n : ℕ) : Ext X X n ≃ₗ[k] Ext Y Y n :=
  (extSourceIso (k := k) e X n).trans (extTargetIso (k := k) Y e n)

@[simp]
theorem selfExtIso_apply (e : X ≅ Y) (n : ℕ) (x : Ext X X n) :
    selfExtIso (k := k) e n x =
      ((Ext.mk₀ e.inv).comp x (zero_add n)).comp (Ext.mk₀ e.hom) (add_zero n) := rfl

theorem selfExtIso_comp (e : X ≅ Y) {i j n : ℕ}
    (x : Ext X X i) (y : Ext X X j) (h : i+j=n) :
    selfExtIso (k := k) e n (x.comp y h) =
      (selfExtIso (k := k) e i x).comp (selfExtIso (k := k) e j y) h := by
  simp only [selfExtIso_apply]
  rw [Ext.comp_assoc_of_second_deg_zero]
  rw [← Ext.comp_assoc_of_third_deg_zero (Ext.mk₀ e.hom)
    ((Ext.mk₀ e.inv).comp y (zero_add j)) (Ext.mk₀ e.hom) (zero_add j)]
  rw [Ext.mk₀_comp_mk₀_assoc, e.hom_inv_id, Ext.mk₀_id_comp]
  rw [← Ext.comp_assoc_of_third_deg_zero]
  rw [Ext.comp_assoc (Ext.mk₀ e.inv) x y (zero_add i) h (by omega)]

@[simp]
theorem selfExtIso_identity (e : X ≅ Y) :
    selfExtIso (k := k) e 0 (Ext.mk₀ (𝟙 X)) = Ext.mk₀ (𝟙 Y) := by
  simp

end ArExplicit

end

end OAI
