import Mathlib

namespace OAI

section
section
noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace LittleFinitistic.DefaultSupport
universe v₁ v₂ v₃ u₁ u₂ u₃
variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {E : Type u₃} [Category.{v₃} E]
lemma mapped_retract (F : C ⥤ D) (G : D ⥤ E) {X Y : C} {Z : E}
    (i : X ⟶ Y) (p : Y ⟶ X) (h : i ≫ p = 𝟙 X) (e : G.obj (F.obj Y) ≅ Z) :
    (G.map (F.map i) ≫ e.hom) ≫ (e.inv ≫ G.map (F.map p)) = 𝟙 _ := by
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [← G.map_comp, ← F.map_comp, h, F.map_id, G.map_id]
lemma mapped_conjugate (F : C ⥤ D) (G : D ⥤ E) {X Y : C} {W : E}
    (p : X ⟶ Y) (i : Y ⟶ X) (a : X ⟶ X) (h : p ≫ i = a)
    (e : W ≅ G.obj (F.obj X)) (c : W ⟶ W)
    (hc : c ≫ e.hom = e.hom ≫ G.map (F.map a)) :
    (e.hom ≫ G.map (F.map p)) ≫ (G.map (F.map i) ≫ e.inv) = c := by
  apply (cancel_mono e.hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [← G.map_comp, ← F.map_comp, h]
  exact hc.symm
lemma mapped_square (F : C ⥤ D) (G : D ⥤ E) {X Y : C} {W : E}
    (a : X ⟶ X) (p : X ⟶ Y) (b : Y ⟶ Y) (h : a ≫ p = p ≫ b)
    (e : W ≅ G.obj (F.obj X)) (c : W ⟶ W)
    (hc : c ≫ e.hom = e.hom ≫ G.map (F.map a)) :
    c ≫ (e.hom ≫ G.map (F.map p)) =
      (e.hom ≫ G.map (F.map p)) ≫ G.map (F.map b) := by
  rw [← Category.assoc, hc, Category.assoc, ← G.map_comp, ← F.map_comp, h]
  simp only [F.map_comp, G.map_comp, Category.assoc]
lemma natural_square (F : C ⥤ D) (S : C ⥤ C) (T : D ⥤ D) (n : S ⋙ F ≅ F ⋙ T)
    {X : C} {Y : D} (e : F.obj X ≅ Y) (a : X ⟶ X) (b : Y ⟶ Y)
    (h : F.map a ≫ e.hom = e.hom ≫ b) :
    F.map (S.map a) ≫ ((n.app X ≪≫ T.mapIso e).hom) =
      (n.app X ≪≫ T.mapIso e).hom ≫ T.map b := by
  have hn := n.hom.naturality a
  have hm := congrArg T.map h
  simp only [Functor.map_comp] at hm
  change _ ≫ (n.hom.app X ≫ T.map e.hom) = (n.hom.app X ≫ T.map e.hom) ≫ _
  rw [← Category.assoc]
  change ((S ⋙ F).map a ≫ n.hom.app X) ≫ T.map e.hom = _
  rw [hn, Category.assoc]
  change _ ≫ (T.map (F.map a) ≫ T.map e.hom) = _
  rw [hm, ← Category.assoc]
lemma biprod_square [HasZeroMorphisms C] [HasZeroMorphisms D]
    [HasBinaryBiproducts C] [HasBinaryBiproducts D]
    (F : C ⥤ D) [F.PreservesZeroMorphisms] [PreservesBinaryBiproducts F]
    {X₁ X₂ : C} {Y₁ Y₂ : D} (e₁ : F.obj X₁ ≅ Y₁) (e₂ : F.obj X₂ ≅ Y₂)
    (a₁ : X₁ ⟶ X₁) (a₂ : X₂ ⟶ X₂) (b₁ : Y₁ ⟶ Y₁) (b₂ : Y₂ ⟶ Y₂)
    (h₁ : F.map a₁ ≫ e₁.hom = e₁.hom ≫ b₁)
    (h₂ : F.map a₂ ≫ e₂.hom = e₂.hom ≫ b₂) :
    F.map (biprod.map a₁ a₂) ≫ (F.mapBiprod _ _ ≪≫ biprod.mapIso e₁ e₂).hom =
      (F.mapBiprod _ _ ≪≫ biprod.mapIso e₁ e₂).hom ≫ biprod.map b₁ b₂ := by
  apply biprod.hom_ext
  · simp only [Iso.trans_hom, Functor.mapBiprod_hom, biprod.mapIso_hom, Category.assoc,
      biprod.map_fst, biprod.map_fst_assoc, biprod.lift_fst_assoc]
    rw [← Category.assoc, ← Functor.map_comp, biprod.map_fst, Functor.map_comp,
      Category.assoc, h₁]
  · simp only [Iso.trans_hom, Functor.mapBiprod_hom, biprod.mapIso_hom, Category.assoc,
      biprod.map_snd, biprod.map_snd_assoc, biprod.lift_snd_assoc]
    rw [← Category.assoc, ← Functor.map_comp, biprod.map_snd, Functor.map_comp,
      Category.assoc, h₂]
end LittleFinitistic.DefaultSupport

end
end
end

end OAI
