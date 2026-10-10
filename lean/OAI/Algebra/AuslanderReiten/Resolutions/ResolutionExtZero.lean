import OAI.Algebra.AuslanderReiten.Resolutions.ResolutionHomology
import OAI.Algebra.AuslanderReiten.Resolutions.ResolutionExtIdentity

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
namespace ArExplicit.ResolutionHomology
universe u v
variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{v} C]
variable {X Y : C} (P : ProjectiveResolution X)

theorem extMk_zeroDegree_eq_zero_iff (f : P.complex.X 0 ⟶ Y)
    (hf : P.complex.d 1 0 ≫ f = 0) : P.extMk f 1 rfl hf = 0 ↔ f = 0 := by
  let := HasDerivedCategory.standard C
  obtain ⟨g,hg⟩ := CokernelCofork.IsColimit.desc' P.isColimitCokernelCofork f hf
  change X ⟶ Y at g
  change P.π.f 0 ≫ g = f at hg
  have he : P.extMk (P.π.f 0 ≫ g) 1 rfl
      (by erw [← Category.assoc, P.complex_d_comp_π_f_zero, zero_comp]) = Ext.mk₀ g := by
    erw [← P.extMk_comp_mk₀ (P.π.f 0) 1 rfl P.complex_d_comp_π_f_zero g,
      ResolutionProducts.extMk_augmentation, Ext.mk₀_id_comp]
    rfl
  have he' : P.extMk f 1 rfl hf = Ext.mk₀ g := by simpa only [hg] using he
  constructor
  · intro hz
    have hg0 : g=0 := Ext.homEquiv₀.symm.injective (by
      change Ext.mk₀ g = Ext.mk₀ (0 : X ⟶ Y)
      erw [← he', hz, Ext.mk₀_zero])
    erw [← hg, hg0, comp_zero]
  · intro hz
    cases hz
    exact P.extMk_zero 1 rfl

end ArExplicit.ResolutionHomology

end

end OAI
