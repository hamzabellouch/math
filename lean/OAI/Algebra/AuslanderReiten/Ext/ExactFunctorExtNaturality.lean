import OAI.Algebra.AuslanderReiten.Resolutions.MapResolutionExtMk

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
namespace ArExplicit.ResolutionProducts
universe u v u' v'
variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{v} C]
variable {D : Type u'} [Category.{v'} D] [Abelian D] [HasExt.{v'} D]
variable (F G : C ⥤ D) [F.Additive] [G.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F] [F.PreservesProjectiveObjects]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G] [G.PreservesProjectiveObjects]
variable (η : F ⟶ G) {X Y : C} (P : ProjectiveResolution X)

def mapResolutionNatHom : ProjectiveResolution.Hom (mapResolution F P)
    (mapResolution G P) (η.app X) where
  hom := (η.mapHomologicalComplex (.down ℕ)).app P.complex
  hom_f_zero_comp_π_f_zero := by
    rw [mapResolution_π_zero, mapResolution_π_zero, ChainComplex.single₀_map_f_zero]
    exact (η.naturality (P.π.f 0)).symm

include P in
theorem mapExactFunctor_natural (n : ℕ) (x : Ext X Y n) :
    (x.mapExactFunctor F).comp (Ext.mk₀ (η.app Y)) (add_zero n) =
      (Ext.mk₀ (η.app X)).comp (x.mapExactFunctor G) (zero_add n) := by
  obtain ⟨f, hf, rfl⟩ := P.extMk_surjective x (n+1) rfl
  rw [map_extMk, map_extMk]
  erw [ProjectiveResolution.extMk_comp_mk₀,
    ProjectiveResolution.mk₀_comp_extMk _ _ _ _ (mapResolutionNatHom F G η P)]
  congr 1
  exact η.naturality f

end ArExplicit.ResolutionProducts

end

end OAI
