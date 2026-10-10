import OAI.Algebra.Finitistic.Rectification.TotalFunctorial

namespace OAI
open CategoryTheory CategoryTheory.Limits HomologicalComplex CochainComplex
open CochainComplex.HomComplex
noncomputable section
namespace LittleFinitistic.RectificationTotal
variable {C D : Type*} [Category C] [Preadditive C] [HasBinaryBiproducts C]
  [Category D] [Preadditive D] [HasBinaryBiproducts D]
variable (F : C ⥤ D) [F.Additive]

abbrev mapComplex := F.mapHomologicalComplex (ComplexShape.up ℤ)

variable {A B A' B' : CochainComplex C ℤ}

/-- The canonical additive comparison for one cone. -/
def coneInterchange (q : A ⟶ B) :
    (mapComplex F).obj (mappingCone q) ≅ mappingCone ((mapComplex F).map q) :=
  homotopyCofiber.mapHomologicalComplexObjIso q F

@[reassoc (attr := simp)]
theorem coneInterchange_inv_inl (q : A ⟶ B) (i j : ℤ) (hij : i + (-1) = j) :
    (mappingCone.inl ((mapComplex F).map q)).v i j hij ≫
      (coneInterchange F q).inv.f j = F.map ((mappingCone.inl q).v i j hij) := by
  exact homotopyCofiber.inlX_mapHomologicalComplexObjXIso_inv q F i j (by change j+1=i; omega)

@[reassoc (attr := simp)]
theorem coneInterchange_inv_inr (q : A ⟶ B) (i : ℤ) :
    (mappingCone.inr ((mapComplex F).map q)).f i ≫
      (coneInterchange F q).inv.f i = F.map ((mappingCone.inr q).f i) := by
  exact homotopyCofiber.inrX_mapHomologicalComplexObjXIso_inv q F i

@[reassoc (attr := simp)]
theorem coneInterchange_hom_inl (q : A ⟶ B) (i j : ℤ) (hij : i + (-1) = j) :
    F.map ((mappingCone.inl q).v i j hij) ≫ (coneInterchange F q).hom.f j =
      (mappingCone.inl ((mapComplex F).map q)).v i j hij := by
  rw [← coneInterchange_inv_inl F q i j hij, Category.assoc]
  rw [← comp_f, Iso.inv_hom_id, id_f, Category.comp_id]

@[reassoc (attr := simp)]
theorem coneInterchange_hom_inr (q : A ⟶ B) (i : ℤ) :
    F.map ((mappingCone.inr q).f i) ≫ (coneInterchange F q).hom.f i =
      (mappingCone.inr ((mapComplex F).map q)).f i := by
  rw [← coneInterchange_inv_inr F q i, Category.assoc]
  rw [← comp_f, Iso.inv_hom_id, id_f, Category.comp_id]

variable {L₀ L₁ L₂ : CochainComplex C ℤ}
variable (p : L₁ ⟶ L₀) (q : L₂ ⟶ L₁) (h : Homotopy (q ≫ p) 0)

/-- Apply the functor to the supplied null-homotopy, transporting only
functorial composition and zero equalities. -/
def mapNullHomotopy : Homotopy ((mapComplex F).map q ≫ (mapComplex F).map p) 0 :=
  (Homotopy.ofEq (by simp)).trans ((F.mapHomotopy h).trans (Homotopy.ofEq (by simp)))

omit [HasBinaryBiproducts C] [HasBinaryBiproducts D] in
@[simp] theorem mapNullHomotopy_hom (i j : ℤ) :
    (mapNullHomotopy F p q h).hom i j = F.map (h.hom i j) := by
  simp [mapNullHomotopy, Homotopy.trans, Homotopy.ofEq]

/-- Mapping the rectifying map agrees with rectifying the mapped data. -/
theorem rectifyingMap_interchange_inv :
    (coneInterchange F q).inv ≫ (mapComplex F).map (rectifyingMap p q h) =
      rectifyingMap ((mapComplex F).map p) ((mapComplex F).map q)
        (mapNullHomotopy F p q h) := by
  ext n
  apply mappingCone.ext_from ((mapComplex F).map q) (n+1) n rfl
  · simp only [comp_f, coneInterchange_inv_inl_assoc]
    dsimp only [mapComplex, Functor.mapHomologicalComplex_map_f]
    rw [← F.map_comp]
    simp [rectifyingMap, Cochain.ofHomotopy]
  · simp only [comp_f, coneInterchange_inv_inr_assoc]
    dsimp only [mapComplex, Functor.mapHomologicalComplex_map_f]
    rw [← F.map_comp]
    simp [rectifyingMap]

theorem rectifyingMap_interchange :
    (coneInterchange F q).hom ≫
      rectifyingMap ((mapComplex F).map p) ((mapComplex F).map q)
        (mapNullHomotopy F p q h) = (mapComplex F).map (rectifyingMap p q h) := by
  rw [← rectifyingMap_interchange_inv F p q h, ← Category.assoc]
  simp

/-- Arbitrary additive functors commute with the actual iterated-cone total. -/
def totalInterchange : (mapComplex F).obj (total p q h) ≅
    total ((mapComplex F).map p) ((mapComplex F).map q) (mapNullHomotopy F p q h) :=
  coneInterchange F (rectifyingMap p q h) ≪≫
    homotopyCofiber.mapArrowIso _ _ (fun j => ⟨j-1, by simp⟩)
      (Arrow.isoMk (coneInterchange F q) (Iso.refl _)
        (by simpa using rectifyingMap_interchange F p q h))

/-- The original zero-column inclusion is carried to the original inclusion. -/
@[reassoc]
theorem inclusion_totalInterchange :
    (mapComplex F).map (inclusion p q h) ≫ (totalInterchange F p q h).hom =
      inclusion ((mapComplex F).map p) ((mapComplex F).map q) (mapNullHomotopy F p q h) := by
  ext n
  change F.map ((mappingCone.inr (rectifyingMap p q h)).f n) ≫
    ((coneInterchange F (rectifyingMap p q h)).hom.f n ≫ _) = _
  rw [coneInterchange_hom_inr_assoc]
  change (mappingCone.inr _).f n ≫ (coneMap _ _ _ _ _).f n = _
  rw [coneMap_inr]
  simp [inclusion]
end LittleFinitistic.RectificationTotal

end

end OAI
