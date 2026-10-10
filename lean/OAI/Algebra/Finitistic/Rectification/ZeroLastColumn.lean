import OAI.Algebra.Finitistic.Rectification.TotalFunctorial
import OAI.Algebra.Finitistic.Rectification.ZeroColumnTotal

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex CochainComplex
namespace LittleFinitistic.ZeroLastColumn
open RectificationTotal
variable {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D]
  [HasBinaryBiproducts C] [HasBinaryBiproducts D]

def coneIso {X Y X' Y' : CochainComplex D ℤ} (p : X ⟶ Y) (p' : X' ⟶ Y')
    (a : X ≅ X') (b : Y ≅ Y') (w : a.hom ≫ p' = p ≫ b.hom) :
    mappingCone p ≅ mappingCone p' where
  hom := coneMap p p' a.hom b.hom w
  inv := coneMap p' p a.inv b.inv (by
    apply (cancel_epi a.hom).1
    simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
    rw [w, Category.assoc, Iso.hom_inv_id, Category.comp_id])
  hom_inv_id := by rw [← coneMap_comp]; simp
  inv_hom_id := by rw [← coneMap_comp]; simp

variable {L₀ L₁ L₂ : CochainComplex C ℤ}
variable (p : L₁ ⟶ L₀) (q : L₂ ⟶ L₁) (h : Homotopy (q ≫ p) 0)
variable (F : C ⥤ D) [F.Additive]

/-- Taking an additive image that kills the relation column leaves precisely the ordinary cone. -/
def mappedTotalIso (h₂ : IsZero ((F.mapHomologicalComplex (.up ℤ)).obj L₂)) :
    (F.mapHomologicalComplex (.up ℤ)).obj (total p q h) ≅
      mappingCone ((F.mapHomologicalComplex (.up ℤ)).map p) := by
  let G := F.mapHomologicalComplex (.up ℤ)
  have hi : IsIso (G.map (mappingCone.inr q)) := by
    rw [← isIso_comp_right_iff _ (mappingCone.mapHomologicalComplexIso q F).hom,
      mappingCone.map_inr]
    exact ZeroColumnTotal.cone_inr_isIso _ h₂
  letI := hi
  refine mappingCone.mapHomologicalComplexIso (rectifyingMap p q h) F ≪≫
    (coneIso (G.map p) (G.map (rectifyingMap p q h))
      (asIso (G.map (mappingCone.inr q))) (Iso.refl _) ?_).symm
  simp only [asIso_hom,Iso.refl_hom,Category.comp_id,← Functor.map_comp]
  congr 1
  simp [rectifyingMap]
end LittleFinitistic.ZeroLastColumn

end

end OAI
