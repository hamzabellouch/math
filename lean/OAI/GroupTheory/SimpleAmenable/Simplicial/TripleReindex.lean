import Mathlib
import OAI.GroupTheory.SimpleAmenable.Simplicial.StageRefinementMonoidal

namespace OAI

section

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory MonoidalCategory Simplicial Opposite
namespace IntervalBar.Diagram

variable {C D : Type} [Groupoid.{0} C] [MonoidalCategory C] [SymmetricCategory C]
  [Groupoid.{0} D] [MonoidalCategory D] [SymmetricCategory D]
variable {I J : Type} [Preorder I] [Preorder J]
noncomputable def diagonalReindex (f : I →o J) :
    Diagram (Diagram (Diagram C J) J) J ⥤ Diagram (Diagram (Diagram C I) I) I :=
  map (map (reindex f)) ⋙ map (reindex f) ⋙ reindex f
noncomputable abbrev map₃ (F : C ⥤ D) [F.Braided] (I : Type) [Preorder I] :=
  map (I:=I) (map (I:=I) (map (I:=I) F))
lemma map₃_diagonalReindex (F:C⥤D) [F.Braided] (f:I→o J) :
    map₃ F J ⋙ diagonalReindex f = diagonalReindex f ⋙ map₃ F I := by
  dsimp only [diagonalReindex,map₃]
  simp only [CategoryTheory.Functor.assoc]
  conv_lhs =>
    rw [←CategoryTheory.Functor.assoc,map_map_map_reindex,CategoryTheory.Functor.assoc]
    enter [2]
    rw [←CategoryTheory.Functor.assoc,map_map_reindex,CategoryTheory.Functor.assoc]
    enter [2]
    rw [←reindex_map]

lemma bar₃_map (n m : SimplexCategoryᵒᵖ) (f : n⟶m) (x : (bar₃ (C:=C)).obj n) :
    (bar₃ (C:=C)).map f x = f.unop.toOrderHom.toFunctor ⋙ x ⋙ diagonalReindex f.unop.toOrderHom := by
  rfl

variable {F G:C⥤D} [F.Braided] [G.Braided]
noncomputable def natTrans₃ (α:F⟶G) [NatTrans.IsMonoidal α] (I:Type) [Preorder I] : map₃ F I ⟶ map₃ G I :=
  mapNatTrans (mapNatTrans (mapNatTrans α))
lemma natTrans₃_reindex (α:F⟶G) [NatTrans.IsMonoidal α] (f:I→o J)
    (A : Diagram (Diagram (Diagram C J) J) J) :
    HEq ((diagonalReindex f).map ((natTrans₃ α J).app A)) ((natTrans₃ α I).app ((diagonalReindex f).obj A)) := by
  have eF := congrArg (fun H=>H.obj A) (map₃_diagonalReindex F f)
  have eG := congrArg (fun H=>H.obj A) (map₃_diagonalReindex G f)
  apply hom_hext eF eG
  intro i j hij
  have eF' := congrArg (fun X=>X.obj i j hij) eF
  have eG' := congrArg (fun X=>X.obj i j hij) eG
  apply hom_hext eF' eG'
  intro k l hkl
  have eF'' := congrArg (fun X=>X.obj k l hkl) eF'
  have eG'' := congrArg (fun X=>X.obj k l hkl) eG'
  apply hom_hext eF'' eG''
  intro p q hpq
  rfl
end IntervalBar.Diagram

end

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory MonoidalCategory Simplicial Opposite
namespace IntervalBar.Diagram

variable {C D : Type} [Groupoid.{0} C] [MonoidalCategory C] [SymmetricCategory C]
  [Groupoid.{0} D] [MonoidalCategory D] [SymmetricCategory D]
  {F G : C ⥤ D} [F.Braided] [G.Braided]
noncomputable def tripleNatTrans (α : F ⟶ G) [NatTrans.IsMonoidal α] (n : ℕ) :
    map (I:=Fin (n+1)) (map (I:=Fin (n+1)) (map (I:=Fin (n+1)) F)) ⟶
      map (I:=Fin (n+1)) (map (I:=Fin (n+1)) (map (I:=Fin (n+1)) G)) :=
  mapNatTrans (mapNatTrans (mapNatTrans α))

noncomputable def homotopyMap₃ (α : F ⟶ G) [NatTrans.IsMonoidal α] :
    bar₃ (C:=C) ⊗ Δ[1] ⟶ bar₃ (C:=D) where
  app n := (NerveHomotopy.homotopyMap (tripleNatTrans α n.unop.len)).app n
  naturality n m f := by
    apply ConcreteCategory.hom_ext
    intro x
    change ((NerveHomotopy.homotopyMap (tripleNatTrans α m.unop.len)).app m
      (((bar₃ (C:=C)).map f x.1), Δ[1].map f x.2)) =
      (bar₃ (C:=D)).map f ((NerveHomotopy.homotopyMap (tripleNatTrans α n.unop.len)).app n x)
    erw [bar₃_map, bar₃_map]
    dsimp only [NerveHomotopy.homotopyMap]
    have hc := NerveHomotopy.cylinder_natural
      (diagonalReindex (C:=C) f.unop.toOrderHom)
      (diagonalReindex (C:=D) f.unop.toOrderHom)
      (natTrans₃ α (Fin (n.unop.len+1))) (natTrans₃ α (Fin (m.unop.len+1)))
      (map₃_diagonalReindex F _) (map₃_diagonalReindex G _)
      (natTrans₃_reindex α _)
    change ((f.unop.toOrderHom.toFunctor ⋙ x.1 ⋙ diagonalReindex f.unop.toOrderHom).prod'
      ((SSet.stdSimplex.objEquiv (Δ[1].map f x.2)).toOrderHom.toFunctor)) ⋙
        NerveHomotopy.cylinder (natTrans₃ α (Fin (m.unop.len+1))) =
      f.unop.toOrderHom.toFunctor ⋙ x.1.prod' ((SSet.stdSimplex.objEquiv x.2).toOrderHom.toFunctor) ⋙
        (NerveHomotopy.cylinder (natTrans₃ α (Fin (n.unop.len+1))) ⋙ diagonalReindex f.unop.toOrderHom)
    erw [hc]
    rfl

noncomputable def bar₃Homotopy (α : F ⟶ G) [NatTrans.IsMonoidal α] :
    SSet.Homotopy (bar₃Map F) (bar₃Map G) where
  h := homotopyMap₃ α
  h₀ := by
    ext n x
    exact congrArg (fun t => t.app n x) (NerveHomotopy.homotopyMap_zero (tripleNatTrans α n.unop.len))
  h₁ := by
    ext n x
    exact congrArg (fun t => t.app n x) (NerveHomotopy.homotopyMap_one (tripleNatTrans α n.unop.len))
  rel := by ext n x; exact x.1.property.elim
lemma bar₃Map_eq_of_monoidalNatTrans (α : F ⟶ G) [NatTrans.IsMonoidal α] (n : ℕ) :
    SSet.homologyMap (bar₃Map F) DiagonalResolution.Z n =
      SSet.homologyMap (bar₃Map G) DiagonalResolution.Z n :=
  (bar₃Homotopy α).congr_homologyMap _ _
end IntervalBar.Diagram

end

end

end OAI
