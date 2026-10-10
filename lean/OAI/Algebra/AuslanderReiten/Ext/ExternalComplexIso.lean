import OAI.Algebra.AuslanderReiten.Tensor.ExternalTensorDifferential

namespace OAI

noncomputable section
namespace ArExplicit.ExternalTensor
open CategoryTheory HomologicalComplex
open scoped TensorProduct
universe u
variable (k A B : Type u) [Field k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]
attribute [local instance] moduleCatBaseModule moduleCatBaseTower
variable {P P' P'' : ChainComplex (ModuleCat.{u} A) ℕ}
  {Q Q' Q'' : ChainComplex (ModuleCat.{u} B) ℕ}

abbrev complexMap (f : P ⟶ P') (g : Q ⟶ Q') :=
  mapBifunctorMap f g (bifunctor k A B) (ComplexShape.down ℕ)

@[reassoc] theorem inclusion_complexMap (f : P ⟶ P') (g : Q ⟶ Q')
    (i j n : ℕ) (h : i+j=n) :
    inclusion k A B P Q i j n h ≫ (complexMap k A B f g).f n =
      mapHom k A B (f.f i) (g.f j) ≫ inclusion k A B P' Q' i j n h := by
  change ιMapBifunctor P Q (bifunctor k A B) (ComplexShape.down ℕ) i j n h ≫
    (mapBifunctorMap f g (bifunctor k A B) (ComplexShape.down ℕ)).f n = _
  erw [ι_mapBifunctorMap]
  change mapHom k A B (f.f i) (𝟙 (Q.X j)) ≫
    mapHom k A B (𝟙 (P'.X i)) (g.f j) ≫ _ = _
  erw [← Category.assoc, ← mapHom_comp, Category.comp_id, Category.id_comp]

@[simp] theorem complexMap_id : complexMap k A B (𝟙 P) (𝟙 Q) = 𝟙 (complex k A B P Q) := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply hom_ext k A B P Q
  intro i j h
  erw [inclusion_complexMap]
  simp only [HomologicalComplex.id_f, mapHom_id, Category.id_comp, Category.comp_id]

theorem complexMap_comp (f : P ⟶ P') (f' : P' ⟶ P'') (g : Q ⟶ Q') (g' : Q' ⟶ Q'') :
    complexMap k A B (f ≫ f') (g ≫ g') = complexMap k A B f g ≫ complexMap k A B f' g' := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply hom_ext k A B P Q
  intro i j h
  erw [inclusion_complexMap k A B (f ≫ f') (g ≫ g') i j n h]
  change mapHom k A B ((f ≫ f').f i) ((g ≫ g').f j) ≫ _ =
    inclusion k A B P Q i j n h ≫ ((complexMap k A B f g).f n ≫ (complexMap k A B f' g').f n)
  erw [← Category.assoc, inclusion_complexMap k A B f g i j n h, Category.assoc,
    inclusion_complexMap k A B f' g' i j n h, HomologicalComplex.comp_f,
    HomologicalComplex.comp_f, mapHom_comp k A B (f.f i) (f'.f i) (g.f j) (g'.f j), Category.assoc]

def complexIso (e : P ≅ P') (f : Q ≅ Q') : complex k A B P Q ≅ complex k A B P' Q' where
  hom := complexMap k A B e.hom f.hom
  inv := complexMap k A B e.inv f.inv
  hom_inv_id := by rw [← complexMap_comp, e.hom_inv_id, f.hom_inv_id, complexMap_id]
  inv_hom_id := by rw [← complexMap_comp, e.inv_hom_id, f.inv_hom_id, complexMap_id]

end ArExplicit.ExternalTensor

end

end OAI
