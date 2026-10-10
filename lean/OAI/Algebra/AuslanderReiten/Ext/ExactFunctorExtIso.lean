import OAI.Algebra.AuslanderReiten.Ext.ExactFunctorExtNaturality
import OAI.Algebra.AuslanderReiten.Ext.ExtIsoFunctor

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
namespace ArExplicit.ResolutionProducts
universe u v
variable {k : Type u} [CommRing k]
variable {C : Type v} [Category.{u} C] [Abelian C] [HasExt.{u} C] [Linear k C]
variable (F G : C ⥤ C) [F.Additive] [G.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F] [F.PreservesProjectiveObjects]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G] [G.PreservesProjectiveObjects]
variable (η : F ≅ G) {X : C} (P : ProjectiveResolution X)

include P in
theorem mapExactFunctor_natIso (n : ℕ) (x : Ext X X n) :
    selfExtIso (k := k) (η.app X) n (x.mapExactFunctor F) = x.mapExactFunctor G := by
  rw [selfExtIso_apply, Ext.comp_assoc_of_third_deg_zero]
  simp only [Iso.app_hom, Iso.app_inv]
  rw [mapExactFunctor_natural F G η.hom P]
  simp

include P in
theorem exactFunctor_action_natIso (E : X ≅ G.obj X) (n : ℕ) (x : Ext X X n) :
    selfExtIso (k := k) (E ≪≫ (η.app X).symm).symm n (x.mapExactFunctor F) =
      selfExtIso (k := k) E.symm n (x.mapExactFunctor G) := by
  rw [← mapExactFunctor_natIso (k := k) F G η P, selfExtIso_trans]
  rfl

end ArExplicit.ResolutionProducts

end

end OAI
