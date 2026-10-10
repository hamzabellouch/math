import Mathlib
import OAI.GroupTheory.SimpleAmenable.Simplicial.EZNatural
import OAI.GroupTheory.SimpleAmenable.Homology.TotalComparison

namespace OAI

section
open CategoryTheory Limits SimplicialObject Simplicial Opposite AlgebraicTopology
open HomologicalComplex HomologicalComplex₂
namespace EilenbergZilber

open DiagonalResolution ModelAssembly
variable {X Y : Dᵒᵖ ⥤ Type} (φ : X ⟶ Y)
noncomputable def bisimplicialMap : bisimplicial X ⟶ bisimplicial Y :=
  Functor.curry.map (Functor.whiskerLeft
    (CategoryTheory.prodOpEquiv SimplexCategory (D:=SimplexCategory)).inverse φ)
lemma level_homology_isIso
    (hφ : ∀ p q,IsIso (SSet.homologyMap ((bisimplicialMap φ).app p) Z q)) (n : ℕ) :
    IsIso (homologyMap (diagonalMap φ) n) := by
  have : IsIso (homologyMap (total.map (twoMap φ) c) n) := by
    apply TotalComparison.total_homology_isIso
    intro p q
    exact hφ (op ⦋p⦌) q
  have he : homologyMap (diagonalMap φ) n =
      (homologyIsoN X n).hom ≫ homologyMap (total.map (twoMap φ) c) n ≫ (homologyIsoN Y n).inv := by
    rw [←Category.assoc,←homology_natural,Category.assoc,Iso.hom_inv_id,Category.comp_id]
  rw [he]
  infer_instance
end EilenbergZilber

end

section

open CategoryTheory MonoidalCategory Simplicial Opposite
namespace NerveHomotopy

universe u v
variable {C D : Type u} [Category.{v} C] [Category.{v} D]
variable {F G : C ⥤ D}

def cylinder (α : F ⟶ G) : C × Fin 2 ⥤ D :=
  CategoryTheory.Functor.uncurry.obj (ComposableArrows.mk₁ α).flip

noncomputable def homotopyMap (α : F ⟶ G) : nerve C ⊗ Δ[1] ⟶ nerve D where
  app n := ↾fun x => x.1.prod' ((SSet.stdSimplex.objEquiv x.2).toOrderHom.toFunctor) ⋙ cylinder α
  naturality _ _ f := by ext x; rfl
@[simp] lemma homotopyMap_zero (α : F ⟶ G) : SSet.ι₀ ≫ homotopyMap α=nerveMap F := by
  ext n x
  apply CategoryTheory.Functor.ext
  · intro i j f
    erw [eqToHom_refl, Category.id_comp, Category.comp_id]
    change F.map (x.map f) ≫ 𝟙 _=F.map (x.map f)
    simp
  · intro i
    rfl
@[simp] lemma homotopyMap_one (α : F ⟶ G) : SSet.ι₁ ≫ homotopyMap α=nerveMap G := by
  ext n x
  apply CategoryTheory.Functor.ext
  · intro i j f
    erw [eqToHom_refl, Category.id_comp, Category.comp_id]
    change G.map (x.map f) ≫ 𝟙 _=G.map (x.map f)
    simp
  · intro i
    rfl

noncomputable def ofNatTrans (α : F ⟶ G) : SSet.Homotopy (nerveMap F) (nerveMap G) where
  h := homotopyMap α
  h₀ := homotopyMap_zero α
  h₁ := homotopyMap_one α
  rel := by ext n x; exact x.1.property.elim

universe w
variable {A : Type w} [Category A] [Preadditive A]
  [Limits.HasCoproducts.{max u v} A] [CategoryWithHomology A]

noncomputable def homologyIso (e : C ≌ D) (R : A) (n : ℕ) :
    (nerve C).homology R n ≅ (nerve D).homology R n where
  hom := SSet.homologyMap (nerveMap e.functor) R n
  inv := SSet.homologyMap (nerveMap e.inverse) R n
  hom_inv_id := by
    rw [←SSet.homologyMap_comp]
    have h := (ofNatTrans e.unitIso.hom).congr_homologyMap R n
    change SSet.homologyMap (nerveMap (e.functor ⋙ e.inverse)) R n = _
    rw [←h]
    exact SSet.homologyMap_id _ _ _
  inv_hom_id := by
    rw [←SSet.homologyMap_comp]
    have h := (ofNatTrans e.counitIso.hom).congr_homologyMap R n
    change SSet.homologyMap (nerveMap (e.inverse ⋙ e.functor)) R n = _
    rw [h]
    exact SSet.homologyMap_id _ _ _

noncomputable instance homologyMap_isIso (F : C ⥤ D) [F.IsEquivalence]
    (R : A) (n : ℕ) : IsIso (SSet.homologyMap (nerveMap F) R n) :=
  (homologyIso F.asEquivalence R n).isIso_hom

end NerveHomotopy

end

open CategoryTheory SimplicialObject Simplicial Opposite AlgebraicTopology
namespace SimplicialDiagonal
open DiagonalResolution

abbrev I := SimplexCategoryᵒᵖ
def uncurry (X : I ⥤ SSet) : DiagonalResolution.Dᵒᵖ ⥤ Type :=
  (prodOpEquiv SimplexCategory (D:=SimplexCategory)).functor ⋙ Functor.uncurry.obj X
def diagonal : (I ⥤ SSet) ⥤ SSet where
  obj X := EilenbergZilber.diag ⋙ uncurry X
  map f := Functor.whiskerLeft EilenbergZilber.diag
    (Functor.whiskerLeft (prodOpEquiv SimplexCategory (D:=SimplexCategory)).functor (Functor.uncurry.map f))
  map_id _ := by ext; rfl
  map_comp _ _ := by ext; rfl
def rowIso (X : I ⥤ SSet) (p : I) :
    (EilenbergZilber.bisimplicial (uncurry X)).obj p ≅ X.obj p :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro q q' f
    simp [EilenbergZilber.bisimplicial,uncurry,Functor.uncurry])
private theorem homologyMap_comp_iso {W X Y Z : SSet} (e : W ≅ X) (f : X ⟶ Y)
    (e' : Y ≅ Z) (q : ℕ) (hf : IsIso (SSet.homologyMap f DiagonalResolution.Z q)) :
    IsIso (SSet.homologyMap (e.hom ≫ f ≫ e'.hom) DiagonalResolution.Z q) := by
  let := hf
  rw [SSet.homologyMap_comp, SSet.homologyMap_comp]
  infer_instance

private theorem row_homologyMap_isIso {X Y : I ⥤ SSet} (f : X ⟶ Y)
    (hf : ∀ p q, IsIso (SSet.homologyMap (f.app p) DiagonalResolution.Z q))
    (p : SimplexCategoryᵒᵖ) (q : ℕ) :
    IsIso (SSet.homologyMap ((EilenbergZilber.bisimplicialMap
      (Functor.whiskerLeft (prodOpEquiv SimplexCategory (D:=SimplexCategory)).functor
        (Functor.uncurry.map f))).app p) DiagonalResolution.Z q) := by
  have he : (EilenbergZilber.bisimplicialMap
      (Functor.whiskerLeft (prodOpEquiv SimplexCategory (D:=SimplexCategory)).functor
        (Functor.uncurry.map f))).app p =
      (rowIso X p).hom ≫ f.app p ≫ (rowIso Y p).inv := by
    ext k x
    rfl
  rw [he]
  exact homologyMap_comp_iso (rowIso X p) (f.app p) (rowIso Y p).symm q (hf p q)

lemma homologyMap_isIso {X Y : I ⥤ SSet} (f : X ⟶ Y)
    (hf : ∀ p q, IsIso (SSet.homologyMap (f.app p) DiagonalResolution.Z q)) (n : ℕ) :
    IsIso (SSet.homologyMap (diagonal.map f) DiagonalResolution.Z n) := by
  exact EilenbergZilber.level_homology_isIso _ (row_homologyMap_isIso f hf) n

def nerveDiagonal : (I ⥤ Cat.{0,0}) ⥤ SSet :=
  (Functor.whiskeringRight I Cat SSet).obj nerveFunctor ⋙ diagonal
lemma nerveDiagonal_isIso {X Y : I ⥤ Cat.{0,0}} (f : X ⟶ Y)
    (hf : ∀ p, (f.app p).toFunctor.IsEquivalence) (n : ℕ) :
    IsIso (SSet.homologyMap (nerveDiagonal.map f) DiagonalResolution.Z n) := by
  apply homologyMap_isIso
  intro p q
  have := hf p
  exact NerveHomotopy.homologyMap_isIso (f.app p).toFunctor DiagonalResolution.Z q
end SimplicialDiagonal

end OAI
