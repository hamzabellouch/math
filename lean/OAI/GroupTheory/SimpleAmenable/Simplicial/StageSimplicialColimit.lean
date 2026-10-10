import Mathlib
import OAI.GroupTheory.SimpleAmenable.Simplicial.TripleBarMaps
import OAI.GroupTheory.SimpleAmenable.Simplicial.StageTripleHomology

namespace OAI

section

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory Limits MonoidalCategory Simplicial Opposite
namespace SimpleAmenable.PolygonObject.LabelledStage.Stage
open IntervalBar IntervalBar.Diagram ColimitTransfer

variable {a n : ℕ} (p q : ℕ)
noncomputable def degreeRowsStage : Stage a n ⥤ (SimplexCategoryᵒᵖ ⥤ Cat.{0,0}) where
  obj S := simplicial (C:=Diagram (Diagram S.Obj (Fin (p+1))) (Fin (q+1)))
  map h := simplicialMap (Diagram.map (I:=Fin (q+1)) (Diagram.map (I:=Fin (p+1)) (inclusion (leOfHom h))))
  map_id S := by
    apply NatTrans.ext; funext r; apply Cat.ext
    exact map₃_inclusion_id r.unop.len q p S
  map_comp h k := by
    apply NatTrans.ext; funext r; apply Cat.ext
    exact map₃_inclusion_comp r.unop.len q p (leOfHom h) (leOfHom k)
noncomputable def degreeRowsCocone : Cocone (degreeRowsStage (a:=a) (n:=n) p q) where
  pt := simplicial (C:=Diagram (Diagram (Labelled a n) (Fin (p+1))) (Fin (q+1)))
  ι := {
    app S := simplicialMap (Diagram.map (I:=Fin (q+1)) (Diagram.map (I:=Fin (p+1)) S.forget))
    naturality S T h := by
      apply NatTrans.ext; funext r; apply Cat.ext
      exact map₃_inclusion_forget r.unop.len q p (leOfHom h) }
noncomputable def degreeHomologyIsColimit (r : SimplexCategoryᵒᵖ) (k:ℕ) :
    IsColimit (((evaluation SimplexCategoryᵒᵖ Cat).obj r ⋙ H k).mapCocone
      (degreeRowsCocone (a:=a) (n:=n) p q)) := by
  let u : degreeRowsStage (a:=a) (n:=n) p q ⋙ (evaluation SimplexCategoryᵒᵖ Cat).obj r ⋙ H k ≅
      tripleHomologyStage r.unop.len q p k :=
    NatIso.ofComponents (fun _ => Iso.refl _) (by
      intro S T h
      simp only [Iso.refl_hom]
      exact (tripleHomologyStage_map r.unop.len q p k h).symm)
  let pointIso : (((evaluation SimplexCategoryᵒᵖ Cat).obj r ⋙ H k).mapCocone
      (degreeRowsCocone (a:=a) (n:=n) p q)).pt ≅
      (tripleHomologyCocone r.unop.len q p k).pt := Iso.refl _
  apply ofIsos _ (tripleHomologyCocone r.unop.len q p k) u.hom pointIso.hom _
    (tripleHomologyIsColimit r.unop.len q p k)
  intro S
  change (H k).map (Diagram.map (I:=Fin (r.unop.len+1))
    (Diagram.map (I:=Fin (q+1)) (Diagram.map (I:=Fin (p+1)) S.forget))).toCatHom ≫ 𝟙 _ =
      (𝟙 _) ≫ (tripleHomologyCocone r.unop.len q p k).ι.app S
  rw [Category.comp_id,Category.id_comp]
  exact (tripleHomologyCocone_ι r.unop.len q p k S).symm
end SimpleAmenable.PolygonObject.LabelledStage.Stage

end

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory Limits Simplicial Opposite
namespace SimplicialDiagonal

variable {J : Type} [Category.{0} J] [IsFiltered J]
noncomputable instance diagonal_preserves : PreservesColimitsOfShape J diagonal := by
  apply preservesColimitsOfShape_of_evaluation
  intro p
  change PreservesColimitsOfShape J (((evaluation I SSet).obj p) ⋙ (evaluation I (Type)).obj p)
  infer_instance
omit [IsFiltered J] in
lemma isIso_of_colimit_fac {A : Type*} [Category A] {F : J ⥤ A}
    {s t : Cocone F} (hs : IsColimit s) (ht : IsColimit t) (u : s.pt ⟶ t.pt)
    (hu : ∀ j,s.ι.app j ≫ u=t.ι.app j) : IsIso u := by
  have he : u=(hs.coconePointUniqueUpToIso ht).hom := by
    apply hs.hom_ext
    intro j
    rw [hu]
    exact (hs.fac t j).symm
  rw [he]
  infer_instance
noncomputable def diagonalHomologyIsColimit {F : J ⥤ (I ⥤ SSet)} (t : Cocone F)
    (ht : ∀ p q, IsColimit (((evaluation I SSet).obj p ⋙
      SSet.homologyFunctor DiagonalResolution.Z q).mapCocone t)) (n:ℕ) :
    IsColimit ((diagonal ⋙ SSet.homologyFunctor DiagonalResolution.Z n).mapCocone t) := by
  let s := colimit.cocone F
  let u : s.pt ⟶ t.pt := colimit.desc F t
  have hrow (p:I) (q:ℕ) : IsIso (SSet.homologyMap (u.app p) DiagonalResolution.Z q) := by
    apply isIso_of_colimit_fac
      (isColimitOfPreserves ((evaluation I SSet).obj p ⋙ SSet.homologyFunctor DiagonalResolution.Z q)
        (colimit.isColimit F)) (ht p q)
    intro j
    change SSet.homologyMap ((s.ι.app j).app p) _ _ ≫ SSet.homologyMap (u.app p) _ _ = _
    rw [←SSet.homologyMap_comp]
    have hu : s.ι.app j ≫ u=t.ι.app j := colimit.ι_desc t j
    have hv := congrArg (fun f : F.obj j ⟶ t.pt => f.app p) hu
    exact congrArg (fun f => SSet.homologyMap f DiagonalResolution.Z q) hv
  haveI := homologyMap_isIso u hrow n
  let G := diagonal ⋙ SSet.homologyFunctor DiagonalResolution.Z n
  change IsColimit (G.mapCocone t)
  haveI : IsIso (G.map u) := homologyMap_isIso u hrow n
  refine IsColimit.ofIsoColimit (isColimitOfPreserves G (colimit.isColimit F))
    (Cocone.ext (c := G.mapCocone s) (c' := G.mapCocone t) (asIso (G.map u)) ?_)
  intro j
  change G.map (s.ι.app j) ≫ G.map u = G.map (t.ι.app j)
  rw [←Functor.map_comp]
  exact congrArg G.map (colimit.ι_desc t j)
end SimplicialDiagonal

end

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory Limits MonoidalCategory Simplicial Opposite
namespace SimpleAmenable.PolygonObject.LabelledStage.Stage
open IntervalBar IntervalBar.Diagram ColimitTransfer SimplicialDiagonal

variable {a n : ℕ}
noncomputable def degreeBarHomologyIsColimit (p q k:ℕ) :
    IsColimit ((nerveDiagonal ⋙ SSet.homologyFunctor DiagonalResolution.Z k).mapCocone
      (degreeRowsCocone (a:=a) (n:=n) p q)) := by
  exact diagonalHomologyIsColimit
    (((Functor.whiskeringRight I Cat SSet).obj nerveFunctor).mapCocone (degreeRowsCocone p q))
    (fun r j => degreeHomologyIsColimit p q r j) k
noncomputable def middleRowsStage (p:ℕ) : Stage a n ⥤ (I ⥤ SSet) where
  obj S := rows₂ (C:=Diagram S.Obj (Fin (p+1)))
  map h := rows₂Map (Diagram.map (I:=Fin (p+1)) (inclusion (leOfHom h)))
  map_id S := by
    apply NatTrans.ext; funext q
    change nerveDiagonal.map ((degreeRowsStage p q.unop.len).map (𝟙 S)) = 𝟙 _
    rw [CategoryTheory.Functor.map_id,CategoryTheory.Functor.map_id]
  map_comp h k := by
    apply NatTrans.ext; funext q
    change nerveDiagonal.map ((degreeRowsStage p q.unop.len).map (h ≫ k)) =
      nerveDiagonal.map ((degreeRowsStage p q.unop.len).map h) ≫
        nerveDiagonal.map ((degreeRowsStage p q.unop.len).map k)
    rw [Functor.map_comp,Functor.map_comp]
noncomputable def middleRowsCocone (p:ℕ) : Cocone (middleRowsStage (a:=a) (n:=n) p) where
  pt := rows₂ (C:=Diagram (Labelled a n) (Fin (p+1)))
  ι := {
    app S := rows₂Map (Diagram.map (I:=Fin (p+1)) S.forget)
    naturality S T h := by
      apply NatTrans.ext; funext q
      change nerveDiagonal.map ((degreeRowsStage p q.unop.len).map h) ≫
        nerveDiagonal.map ((degreeRowsCocone p q.unop.len).ι.app T) =
          nerveDiagonal.map ((degreeRowsCocone p q.unop.len).ι.app S)
      rw [←Functor.map_comp,Cocone.w] }
noncomputable def middleBarHomologyIsColimit (p k:ℕ) :
    IsColimit ((diagonal ⋙ SSet.homologyFunctor DiagonalResolution.Z k).mapCocone
      (middleRowsCocone (a:=a) (n:=n) p)) := by
  apply diagonalHomologyIsColimit
  intro q j
  exact degreeBarHomologyIsColimit p q.unop.len j
noncomputable def topRowsStage : Stage a n ⥤ (I ⥤ SSet) where
  obj S := rows₃ (C:=S.Obj)
  map h := rows₃Map (inclusion (leOfHom h))
  map_id S := by
    apply NatTrans.ext; funext p
    change diagonal.map ((middleRowsStage p.unop.len).map (𝟙 S)) = 𝟙 _
    rw [CategoryTheory.Functor.map_id,CategoryTheory.Functor.map_id]
  map_comp h k := by
    apply NatTrans.ext; funext p
    change diagonal.map ((middleRowsStage p.unop.len).map (h ≫ k)) =
      diagonal.map ((middleRowsStage p.unop.len).map h) ≫
        diagonal.map ((middleRowsStage p.unop.len).map k)
    rw [Functor.map_comp,Functor.map_comp]
noncomputable def topRowsCocone : Cocone (topRowsStage (a:=a) (n:=n)) where
  pt := rows₃ (C:=Labelled a n)
  ι := {
    app S := rows₃Map S.forget
    naturality S T h := by
      apply NatTrans.ext; funext p
      change diagonal.map ((middleRowsStage p.unop.len).map h) ≫
        diagonal.map ((middleRowsCocone p.unop.len).ι.app T) =
          diagonal.map ((middleRowsCocone p.unop.len).ι.app S)
      rw [←Functor.map_comp,Cocone.w] }

noncomputable def tripleBarHomologyIsColimit (k:ℕ) :
    IsColimit ((diagonal ⋙ SSet.homologyFunctor DiagonalResolution.Z k).mapCocone
      (topRowsCocone (a:=a) (n:=n))) := by
  apply diagonalHomologyIsColimit
  intro p j
  exact middleBarHomologyIsColimit p.unop.len j
end SimpleAmenable.PolygonObject.LabelledStage.Stage

end

end

end OAI
