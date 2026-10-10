import OAI.Algebra.AuslanderReiten.Resolutions.MapResolutionExtMk

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
namespace ArExplicit.ResolutionProducts
universe u v u' v'
variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{v} C]
variable {D : Type u'} [Category.{v'} D] [Abelian D] [HasExt.{v'} D]
variable (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F]
  [PreservesFiniteColimits F] [F.PreservesProjectiveObjects]
variable {X : C} {Y : D} (P : ProjectiveResolution X) (Q : ProjectiveResolution Y)

theorem map_extMk_comparison (e : Y ≅ F.obj X)
    (φ : ProjectiveResolution.Hom Q (mapResolution F P) e.hom)
    {n : ℕ} (f : P.complex.X n ⟶ X) (hf : P.complex.d (n+1) n ≫ f = 0)
    (g : Q.complex.X n ⟶ Y) (hg : Q.complex.d (n+1) n ≫ g = 0)
    (hgf : g = (φ.hom.f n ≫ F.map f) ≫ e.inv) :
    ((Ext.mk₀ e.hom).comp ((P.extMk f (n+1) rfl hf).mapExactFunctor F) (zero_add n)).comp
      (Ext.mk₀ e.inv) (add_zero n) = Q.extMk g (n+1) rfl hg := by
  subst g
  erw [map_extMk, ProjectiveResolution.mk₀_comp_extMk _ _ _ _ φ,
    ProjectiveResolution.extMk_comp_mk₀]

end ArExplicit.ResolutionProducts

end

end OAI
