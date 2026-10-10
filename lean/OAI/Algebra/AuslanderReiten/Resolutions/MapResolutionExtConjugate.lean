import OAI.Algebra.AuslanderReiten.Resolutions.MapResolutionExtMk

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
namespace ArExplicit.ResolutionProducts
universe u v
variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{v} C]
variable (F : C ⥤ C) [F.Additive] [PreservesFiniteLimits F]
  [PreservesFiniteColimits F] [F.PreservesProjectiveObjects]
variable {X Y : C} (P : ProjectiveResolution X) {n : ℕ}

theorem map_extMk_conjugate (a : X ⟶ F.obj X) (b : F.obj Y ⟶ Y)
    (φ : ProjectiveResolution.Hom P (mapResolution F P) a)
    (f : P.complex.X n ⟶ Y) (hf : P.complex.d (n+1) n ≫ f = 0)
    (g : P.complex.X n ⟶ Y) (hg : P.complex.d (n+1) n ≫ g = 0)
    (hgf : g = (φ.hom.f n ≫ F.map f) ≫ b) :
    ((Ext.mk₀ a).comp ((P.extMk f (n+1) rfl hf).mapExactFunctor F) (zero_add n)).comp
      (Ext.mk₀ b) (add_zero n) =
        P.extMk g (n+1) rfl hg := by
  subst g
  erw [map_extMk, ProjectiveResolution.mk₀_comp_extMk _ _ _ _ φ,
    ProjectiveResolution.extMk_comp_mk₀]

end ArExplicit.ResolutionProducts

end

end OAI
