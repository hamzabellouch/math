import OAI.Algebra.AuslanderReiten.Ext.ExtIsoFunctor

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
namespace ArExplicit
universe u v
variable {k : Type u} [CommRing k]
variable {C : Type v} [Category.{u} C] [Abelian C] [HasExt.{u} C] [Linear k C]
variable (F : C ⥤ C) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
variable {X Y : C} (e : X ≅ Y) (E : Y ≅ F.obj Y)

theorem exactFunctor_scalar_transport (n : ℕ) (c : k)
    (h : ∀ z : Ext Y Y n, selfExtIso (k := k) E.symm n (z.mapExactFunctor F) = c • z)
    (x : Ext X X n) :
    selfExtIso (k := k) (e ≪≫ E ≪≫ F.mapIso e.symm).symm n (x.mapExactFunctor F) = c • x := by
  have ht := selfExtIso_conjugated_functor (k := k) F e.symm E n x
  simp only [Iso.symm_symm_eq] at ht
  rw [← ht, h, map_smul]
  congr 1
  simp [selfExtIso_apply]

end ArExplicit

end

end OAI
