import Mathlib.Algebra.Homology.BifunctorHomotopy

namespace OAI

noncomputable section

namespace ArExplicit

open CategoryTheory CategoryTheory.Limits HomologicalComplex

universe u₁ u₂ u₃ v₁ v₂ v₃

variable {C₁ : Type u₁} {C₂ : Type u₂} {D : Type u₃}
  [Category.{v₁} C₁] [Category.{v₂} C₂] [Category.{v₃} D]
  [Preadditive C₁] [Preadditive C₂] [Preadditive D]
  {c : ComplexShape ℕ} [TotalComplexShape c c c]
  (F : C₁ ⥤ C₂ ⥤ D) [F.Additive] [∀ X, (F.obj X).Additive]
  [∀ (P : HomologicalComplex C₁ c) (Q : HomologicalComplex C₂ c),
    HasMapBifunctor P Q F c]

theorem totalMap_id (P : HomologicalComplex C₁ c) (Q : HomologicalComplex C₂ c) :
    mapBifunctorMap (𝟙 P) (𝟙 Q) F c = 𝟙 _ := by
  ext n : 1
  apply mapBifunctor.hom_ext
  intro i j h
  simp

theorem totalMap_comp {P P' P'' : HomologicalComplex C₁ c}
    {Q Q' Q'' : HomologicalComplex C₂ c} (f : P ⟶ P') (f' : P' ⟶ P'')
    (g : Q ⟶ Q') (g' : Q' ⟶ Q'') :
    mapBifunctorMap f g F c ≫
      mapBifunctorMap f' g' F c =
    mapBifunctorMap (f ≫ f') (g ≫ g') F c := by
  ext n : 1
  apply mapBifunctor.hom_ext
  intro i j h
  simp only [comp_f, Category.assoc, ι_mapBifunctorMap_assoc, ι_mapBifunctorMap,
    Functor.map_comp, NatTrans.comp_app]
  simp only [NatTrans.naturality_assoc]

def totalHomotopyEquiv {P P' : HomologicalComplex C₁ c} {Q Q' : HomologicalComplex C₂ c}
    (e : HomotopyEquiv P P') (f : HomotopyEquiv Q Q') :
    HomotopyEquiv (mapBifunctor P Q F c)
      (mapBifunctor P' Q' F c) where
  hom := mapBifunctorMap e.hom f.hom F c
  inv := mapBifunctorMap e.inv f.inv F c
  homotopyHomInvId :=
    (Homotopy.ofEq (totalMap_comp F e.hom e.inv f.hom f.inv)).trans
      ((mapBifunctorMapHomotopy₁ e.homotopyHomInvId (f.hom ≫ f.inv) F
        c).trans
        ((mapBifunctorMapHomotopy₂ (𝟙 P) f.homotopyHomInvId F
          c).trans (Homotopy.ofEq (totalMap_id F P Q))))
  homotopyInvHomId :=
    (Homotopy.ofEq (totalMap_comp F e.inv e.hom f.inv f.hom)).trans
      ((mapBifunctorMapHomotopy₁ e.homotopyInvHomId (f.inv ≫ f.hom) F
        c).trans
        ((mapBifunctorMapHomotopy₂ (𝟙 P') f.homotopyInvHomId F
          c).trans (Homotopy.ofEq (totalMap_id F P' Q'))))

end ArExplicit

end

end OAI
