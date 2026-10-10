import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace LittleFinitistic.FiniteSumTransport
variable {C D E : Type*} [Category C] [Category D] [Category E]
  [Preadditive C] [Preadditive D] [Preadditive E]
  [HasFiniteBiproducts C] [HasFiniteBiproducts D]
variable (F : C ⥤ E) (G : D ⥤ E) [F.Additive] [G.Additive]
variable {I : Type} [Finite I] (X : I → C) (Y : I → D)
variable (α : ∀ i, F.obj (X i) ≅ G.obj (Y i))

def iso : F.obj (⨁ X) ≅ G.obj (⨁ Y) :=
  F.mapBiproduct X ≪≫ biproduct.mapIso α ≪≫ (G.mapBiproduct Y).symm

@[reassoc (attr := simp)]
theorem injection (i : I) :
    F.map (biproduct.ι X i) ≫ (iso F G X Y α).hom =
      (α i).hom ≫ G.map (biproduct.ι Y i) := by
  have hi : F.map (biproduct.ι X i) ≫ (F.mapBiproduct X).hom =
      biproduct.ι (fun j => F.obj (X j)) i := by
    apply (cancel_mono (F.mapBiproduct X).inv).1
    rw [Category.assoc,Iso.hom_inv_id,Category.comp_id]
    simp only [Functor.mapBiproduct_inv,biproduct.ι_desc]
  simp only [iso,Iso.trans_hom,Iso.symm_hom,← Category.assoc,hi]
  simp [biproduct.mapIso_hom]
  erw [Category.assoc, biproduct.ι_desc]
  rfl

/-- Coordinate isomorphisms commute with the supplied map from a finite sum. -/
theorem desc_square {U : C} {V : D} (β : F.obj U ≅ G.obj V)
    (f : ∀ i, X i ⟶ U) (g : ∀ i, Y i ⟶ V)
    (h : ∀ i, (α i).hom ≫ G.map (g i) = F.map (f i) ≫ β.hom) :
    (iso F G X Y α).hom ≫ G.map (biproduct.desc g) =
      F.map (biproduct.desc f) ≫ β.hom := by
  apply (cancel_epi (F.mapBiproduct X).inv).1
  apply biproduct.hom_ext'
  intro i
  simp only [Functor.mapBiproduct_inv,biproduct.ι_desc_assoc]
  rw [← Category.assoc,injection,Category.assoc,← Functor.map_comp,
    biproduct.ι_desc,h]
  rw [← Category.assoc,← Functor.map_comp,biproduct.ι_desc]

@[reassoc (attr := simp)]
theorem projection (i : I) :
    (iso F G X Y α).hom ≫ G.map (biproduct.π Y i) =
      F.map (biproduct.π X i) ≫ (α i).hom := by
  apply (cancel_epi (F.mapBiproduct X).inv).1
  apply biproduct.hom_ext'
  intro j
  simp only [Functor.mapBiproduct_inv,biproduct.ι_desc_assoc]
  rw [← Category.assoc,injection,Category.assoc,← Functor.map_comp,
    ← Category.assoc (F.map (biproduct.ι X j)),← Functor.map_comp]
  classical
  by_cases hji : j=i
  · subst j; simp
  · simp [hji]

/-- Entrywise coordinate squares identify the entire supplied finite matrix map. -/
theorem matrix_square {J : Type} [Finite J] (X' : J → C) (Y' : J → D)
    (β : ∀ j, F.obj (X' j) ≅ G.obj (Y' j))
    (f : (⨁ X) ⟶ (⨁ X')) (g : (⨁ Y) ⟶ (⨁ Y'))
    (h : ∀ i j, (α i).hom ≫ G.map (biproduct.ι Y i ≫ g ≫ biproduct.π Y' j) =
      F.map (biproduct.ι X i ≫ f ≫ biproduct.π X' j) ≫ (β j).hom) :
    (iso F G X Y α).hom ≫ G.map g = F.map f ≫ (iso F G X' Y' β).hom := by
  apply (cancel_epi (F.mapBiproduct X).inv).1
  apply biproduct.hom_ext'
  intro i
  simp only [Functor.mapBiproduct_inv,biproduct.ι_desc_assoc]
  apply (cancel_mono (G.mapBiproduct Y').hom).1
  apply biproduct.hom_ext
  intro j
  have hp : (G.mapBiproduct Y').hom ≫ biproduct.π (G.obj ∘ Y') j =
      G.map (biproduct.π Y' j) := by
    change (biproduct.lift (fun j => G.map (biproduct.π Y' j))) ≫
      biproduct.π (fun j => G.obj (Y' j)) j = _
    exact biproduct.lift_π _ j
  simp only [Category.assoc,hp,injection_assoc,projection]
  simpa only [Functor.map_comp,Category.assoc] using h i j
end LittleFinitistic.FiniteSumTransport

end

end OAI
