import OAI.Algebra.AuslanderReiten.Homology.VectorCochainNaturality

namespace OAI

noncomputable section
namespace ArExplicit.VectorCochain
open CategoryTheory CategoryTheory.Limits HomologicalComplex
universe u
variable (k : Type u) [Field k]
variable (F : ModuleCat.{u} k ⥤ ModuleCat.{u} k ⥤ ModuleCat.{u} k)
  [F.Additive] [∀ X, (F.obj X).Additive]

@[simp, reassoc] theorem totalZeroHomologyIso_π
    (X Y : ℕ → ModuleCat.{u} k) (n : ℕ) :
    (mapBifunctor (zeroDifferential k X) (zeroDifferential k Y) F (.up ℕ)).homologyπ n ≫
      (totalZeroHomologyIso k F X Y n).hom =
    (mapBifunctor (zeroDifferential k X) (zeroDifferential k Y) F (.up ℕ)).iCycles n := by
  let K := mapBifunctor (zeroDifferential k X) (zeroDifferential k Y) F (.up ℕ)
  let a := K.isoHomologyπ ((ComplexShape.up ℕ).prev n) n rfl
    (total_zero_differential k F X Y _ _)
  let b := K.iCyclesIso n ((ComplexShape.up ℕ).next n) rfl
    (total_zero_differential k F X Y _ _)
  change a.hom ≫ a.inv ≫ b.hom = b.hom
  exact a.hom_inv_id_assoc _

@[reassoc] theorem totalZeroHomologyIso_natural
    {X Y X' Y' : ℕ → ModuleCat.{u} k}
    (f : mapBifunctor (zeroDifferential k X) (zeroDifferential k Y) F (.up ℕ) ⟶
      mapBifunctor (zeroDifferential k X') (zeroDifferential k Y') F (.up ℕ)) (n : ℕ) :
    homologyMap f n ≫ (totalZeroHomologyIso k F X' Y' n).hom =
      (totalZeroHomologyIso k F X Y n).hom ≫ f.f n := by
  apply (cancel_epi ((mapBifunctor (zeroDifferential k X)
    (zeroDifferential k Y) F (.up ℕ)).homologyπ n)).1
  rw [homologyπ_naturality_assoc, totalZeroHomologyIso_π, ← Category.assoc,
    totalZeroHomologyIso_π]
  simp

@[reassoc] theorem totalZeroHomologyIso_inv_natural
    {X Y X' Y' : ℕ → ModuleCat.{u} k}
    (f : mapBifunctor (zeroDifferential k X) (zeroDifferential k Y) F (.up ℕ) ⟶
      mapBifunctor (zeroDifferential k X') (zeroDifferential k Y') F (.up ℕ)) (n : ℕ) :
    (totalZeroHomologyIso k F X Y n).inv ≫ homologyMap f n =
      f.f n ≫ (totalZeroHomologyIso k F X' Y' n).inv := by
  apply (cancel_mono (totalZeroHomologyIso k F X' Y' n).hom).1
  simp only [Category.assoc, totalZeroHomologyIso_natural,
    Iso.inv_hom_id, Category.comp_id, Iso.inv_hom_id_assoc]

variable {P P' Q Q' : CochainComplex (ModuleCat.{u} k) ℕ}

def tensorRepresentativesNaturality (f : P ⟶ P') (g : Q ⟶ Q') :
    Homotopy
      (mapBifunctorMap (representatives k P) (representatives k Q) F (.up ℕ) ≫
        mapBifunctorMap f g F (.up ℕ))
      (mapBifunctorMap (gradedMap k f) (gradedMap k g) F (.up ℕ) ≫
        mapBifunctorMap (representatives k P') (representatives k Q') F (.up ℕ)) :=
  (Homotopy.ofEq (totalMap_comp F _ _ _ _)).trans
    ((mapBifunctorMapHomotopy₁ (representativesNaturality k f)
      (representatives k Q ≫ g) F (.up ℕ)).trans
      ((mapBifunctorMapHomotopy₂ (gradedMap k f ≫ representatives k P')
        (representativesNaturality k g) F (.up ℕ)).trans
        (Homotopy.ofEq (totalMap_comp F _ _ _ _).symm)))

@[reassoc] theorem kunnethIso_inv_natural (f : P ⟶ P') (g : Q ⟶ Q') (n : ℕ) :
    (kunnethIso k F P Q n).inv ≫ homologyMap (mapBifunctorMap f g F (.up ℕ)) n =
      (mapBifunctorMap (gradedMap k f) (gradedMap k g) F (.up ℕ)).f n ≫
        (kunnethIso k F P' Q' n).inv := by
  rw [kunnethIso_inv, kunnethIso_inv]
  rw [Category.assoc, ← homologyMap_comp,
    (tensorRepresentativesNaturality k F f g).homologyMap_eq,
    homologyMap_comp, ← Category.assoc, totalZeroHomologyIso_inv_natural]
  exact Category.assoc _ _ _

@[reassoc] theorem kunnethIso_natural (f : P ⟶ P') (g : Q ⟶ Q') (n : ℕ) :
    homologyMap (mapBifunctorMap f g F (.up ℕ)) n ≫ (kunnethIso k F P' Q' n).hom =
      (kunnethIso k F P Q n).hom ≫
        (mapBifunctorMap (gradedMap k f) (gradedMap k g) F (.up ℕ)).f n := by
  apply (cancel_epi (kunnethIso k F P Q n).inv).1
  simp only [← Category.assoc]
  rw [kunnethIso_inv_natural, Iso.inv_hom_id, Category.id_comp, Category.assoc,
    Iso.inv_hom_id, Category.comp_id]

end ArExplicit.VectorCochain

end

end OAI
