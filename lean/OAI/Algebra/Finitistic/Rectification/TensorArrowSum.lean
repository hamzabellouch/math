import OAI.Algebra.Finitistic.Encoding.ArrowBasisIso

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace LittleFinitistic.TensorArrowSum
universe u
variable (k : Type u) [Field k] (d : ℕ)

def insertion (a : Fin (d+1)) : ModuleCat.of k k ⟶ ModuleCat.of k (QuadraticEncoding.Arrows k d) :=
  biproduct.ι (ArrowBasisIso.family k d) a ≫ (ArrowBasisIso.iso k d).hom

@[simp] theorem insertion_apply (a : Fin (d+1)) (c : k) :
    (insertion k d a).hom c = c • QuadraticEncoding.basis a :=
  ArrowBasisIso.injection_apply k d a c

/-- An additive realization of the actual arrow-basis sum is an isomorphism. -/
theorem desc_isIso {C : Type*} [Category C] [Preadditive C] [HasFiniteBiproducts C]
    (F : ModuleCat.{u} k ⥤ C) [F.Additive] :
    IsIso (biproduct.desc (fun a : Fin (d+1) => F.map (insertion k d a))) := by
  have he : biproduct.desc (fun a : Fin (d+1) => F.map (insertion k d a)) =
      (F.mapBiproduct (ArrowBasisIso.family k d)).inv ≫ F.map (ArrowBasisIso.iso k d).hom := by
    apply biproduct.hom_ext'
    intro a
    simp only [insertion, Functor.map_comp, Functor.mapBiproduct_inv]
    erw [biproduct.ι_desc, biproduct.ι_desc_assoc]
  rw [he]
  infer_instance

/-- Coordinate isomorphisms identify an actual arrow family with the realized basis. -/
theorem desc_isIso_of_coordinates {C : Type*} [Category C] [Preadditive C]
    [HasFiniteBiproducts C] (F : ModuleCat.{u} k ⥤ C) [F.Additive]
    (X : Fin (d+1) → C) (Y : C) (α : ∀ a, X a ≅ F.obj (ModuleCat.of k k))
    (β : Y ≅ F.obj (ModuleCat.of k (QuadraticEncoding.Arrows k d)))
    (f : ∀ a, X a ⟶ Y)
    (hf : ∀ a, (α a).hom ≫ F.map (insertion k d a) = f a ≫ β.hom) :
    IsIso (biproduct.desc f) := by
  have he : biproduct.desc f ≫ β.hom =
      (biproduct.mapIso α).hom ≫ biproduct.desc (fun a => F.map (insertion k d a)) := by
    apply biproduct.hom_ext'
    intro a
    simp only [biproduct.mapIso_hom,biproduct.ι_desc_assoc,biproduct.ι_map_assoc,biproduct.ι_desc]
    exact (hf a).symm
  let := desc_isIso k d F
  rw [← isIso_comp_right_iff _ β.hom,he]
  infer_instance
end LittleFinitistic.TensorArrowSum

end

end OAI
