import OAI.Algebra.AuslanderReiten.Coordinates.MapExtend

namespace OAI

noncomputable section
open CategoryTheory Category Limits ZeroObject HomologicalComplex
namespace ArExplicit.ResolutionProducts
universe u v u' v'
variable {C : Type u} [Category.{v} C] [Abelian C]
variable {D : Type u'} [Category.{v'} D] [Abelian D]
variable (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
variable [F.PreservesProjectiveObjects]
variable {X : C} (P : ProjectiveResolution X)

omit [Abelian C] [Abelian D] [F.Additive] [PreservesFiniteLimits F]
  [PreservesFiniteColimits F] [F.PreservesProjectiveObjects] in
private theorem map_composite_cancel {U V W Z : C} {U' Z' : D}
    (a : U' ⟶ F.obj U) (b : U ⟶ V) (f : V ⟶ W) (e : W ≅ Z) (t : F.obj W ⟶ Z') :
    a ≫ F.map (b ≫ f ≫ e.hom) ≫ (F.map e.inv ≫ t) =
      (a ≫ F.map b) ≫ F.map f ≫ t := by
  simp only [Functor.map_comp, Category.assoc]
  rw [← F.map_comp_assoc e.hom e.inv t, e.hom_inv_id, F.map_id, id_comp]

def mapResolutionCochainIso : (mapResolution F P).cochainComplex ≅
    (F.mapHomologicalComplex (.up ℤ)).obj P.cochainComplex :=
  mapExtendIso F P.complex ComplexShape.embeddingDownNat

theorem mapResolutionCochainIso_coordinate (n : ℤ) (j : ℕ) (h : -(j : ℤ) = n) :
    (mapResolutionCochainIso F P).hom.f n ≫ F.map (P.cochainComplexXIso n j h).hom =
      ((mapResolution F P).cochainComplexXIso n j h).hom :=
  mapExtendXIso_hom_XIso F P.complex (ComplexShape.embeddingDownNat.r_eq_some h)

theorem mapResolution_π_zero : (mapResolution F P).π.f 0 = F.map (P.π.f 0) := by
  change F.map (P.π.f 0) ≫ ((singleMapHomologicalComplex F (.down ℕ) 0).hom.app X).f 0 = _
  rw [singleMapHomologicalComplex_hom_app_self]
  change F.map (P.π.f 0) ≫ (F.map (𝟙 X) ≫ 𝟙 (F.obj X)) = _
  simp

theorem mapResolutionCochainIso_π :
    (mapResolutionCochainIso F P).hom ≫
      (F.mapHomologicalComplex (.up ℤ)).map P.π' ≫
        (F.mapCochainComplexSingleFunctor 0).hom.app X = (mapResolution F P).π' := by
  apply to_single_hom_ext
  change (mapResolutionCochainIso F P).hom.f 0 ≫ F.map (P.π'.f 0) ≫
    ((singleMapHomologicalComplex F (.up ℤ) 0).hom.app X).f 0 = (mapResolution F P).π'.f 0
  rw [P.π'_f_zero,
    (mapResolution F P).π'_f_zero, mapResolution_π_zero,
    singleMapHomologicalComplex_hom_app_self]
  have he := map_composite_cancel F ((mapResolutionCochainIso F P).hom.f 0)
    (P.cochainComplexXIso 0 0 (by simp)).hom (show P.complex.X 0 ⟶ X from P.π.f 0)
    (singleObjXSelf (.up ℤ) 0 X).symm (singleObjXSelf (.up ℤ) 0 (F.obj X)).inv
  exact he.trans (congrArg (fun a => a ≫ F.map (P.π.f 0) ≫
    (singleObjXSelf (.up ℤ) 0 (F.obj X)).inv) (mapResolutionCochainIso_coordinate F P 0 0 (by simp)))

end ArExplicit.ResolutionProducts

end

end OAI
