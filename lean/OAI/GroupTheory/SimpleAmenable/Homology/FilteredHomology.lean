import Mathlib
import OAI.GroupTheory.SimpleAmenable.Simplicial.StageNerveColimit

namespace OAI

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
namespace FilteredHomology

variable {J : Type} [Category.{0} J] [IsFiltered J]
abbrev A := ModuleCat.{0} ℤ
abbrev c := ComplexShape.down ℕ
noncomputable def complex (F : J ⥤ ChainComplex A ℕ) : ChainComplex (J ⥤ A) ℕ where
  X i := F ⋙ HomologicalComplex.eval A c i
  d i j := { app t := (F.obj t).d i j
             naturality _ _ f := (F.map f).comm i j }
  shape i j h := by apply NatTrans.ext; funext t; exact (F.obj t).shape i j h
  d_comp_d' i j k _ _ := by apply NatTrans.ext; funext t; exact (F.obj t).d_comp_d i j k
noncomputable def injection (j : J) : (evaluation J A).obj j ⟶ colim where
  app F := colimit.ι F j
  naturality _ _ f := (colimit.ι_map f j).symm
noncomputable def cocone (F : J ⥤ ChainComplex A ℕ) : Cocone F where
  pt := (colim.mapHomologicalComplex c).obj (complex F)
  ι := {
    app j := {
      f i := colimit.ι ((complex F).X i) j
      comm' i k _ := colimit.ι_map ((complex F).d i k) j }
    naturality i j f := by
      apply HomologicalComplex.Hom.ext; funext n
      exact colimit.w (F ⋙ HomologicalComplex.eval A c n) f }
noncomputable def isColimit (F : J ⥤ ChainComplex A ℕ) : IsColimit (cocone F) :=
  HomologicalComplex.isColimitOfEval F (cocone F) (fun _ => colimit.isColimit _)
noncomputable def evaluationHomology (F : J ⥤ ChainComplex A ℕ) (n : ℕ) (j:J) :
    (F.obj j).homology n ≅ ((complex F).homology n).obj j :=
  ((complex F).sc n).mapHomologyIso ((evaluation J A).obj j)
noncomputable def colimitHomology (F : J ⥤ ChainComplex A ℕ) (n : ℕ) :
    (cocone F).pt.homology n ≅ colimit ((complex F).homology n) :=
  ((complex F).sc n).mapHomologyIso colim
lemma homology_injection (F : J ⥤ ChainComplex A ℕ) (n : ℕ) (j:J) :
    HomologicalComplex.homologyMap ((cocone F).ι.app j) n =
      (evaluationHomology F n j).hom ≫ colimit.ι ((complex F).homology n) j ≫
        (colimitHomology F n).inv :=
  ShortComplex.homologyMap_mapNatTrans ((complex F).sc n) (injection j)
omit [IsFiltered J] in
lemma evaluationHomology_naturality (F : J ⥤ ChainComplex A ℕ) (n : ℕ) {i j:J} (f:i⟶j) :
    HomologicalComplex.homologyMap (F.map f) n ≫ (evaluationHomology F n j).hom =
      (evaluationHomology F n i).hom ≫ ((complex F).homology n).map f := by
  have h := ShortComplex.homologyMap_mapNatTrans ((complex F).sc n) ((evaluation J A).map f)
  change HomologicalComplex.homologyMap (F.map f) n =
    (evaluationHomology F n i).hom ≫ ((complex F).homology n).map f ≫
      (evaluationHomology F n j).inv at h
  rw [h]
  simp [Category.assoc]
noncomputable def homologyCocone (F : J ⥤ ChainComplex A ℕ) (n : ℕ)
    (d : Cocone (F ⋙ HomologicalComplex.homologyFunctor A c n)) :
    Cocone ((complex F).homology n) where
  pt := d.pt
  ι := { app j := (evaluationHomology F n j).inv ≫ d.ι.app j
         naturality i j f := by
           have h := evaluationHomology_naturality F n f
           rw [←Iso.inv_comp_eq] at h
           erw [Category.assoc ((evaluationHomology F n i).inv), ←h]
           erw [Category.assoc ((evaluationHomology F n i).inv),
             Category.assoc (HomologicalComplex.homologyMap (F.map f) n),
             Iso.hom_inv_id_assoc (evaluationHomology F n j)]
           simp only [Functor.const_obj_map]
           exact congrArg (fun t => (evaluationHomology F n i).inv ≫ t) (d.w f) }
noncomputable def homologyIsColimit (F : J ⥤ ChainComplex A ℕ) (n : ℕ) :
    IsColimit ((HomologicalComplex.homologyFunctor A c n).mapCocone (cocone F)) where
  desc d := (colimitHomology F n).hom ≫ colimit.desc _ (homologyCocone F n d)
  fac d j := by
    change HomologicalComplex.homologyMap ((cocone F).ι.app j) n ≫ _ = _
    rw [homology_injection]
    erw [Category.assoc (evaluationHomology F n j).hom,
      Category.assoc (colimit.ι ((complex F).homology n) j),
      Iso.inv_hom_id_assoc (colimitHomology F n), colimit.ι_desc]
    change (evaluationHomology F n j).hom ≫ ((evaluationHomology F n j).inv ≫ d.ι.app j) = _
    exact Iso.hom_inv_id_assoc _ _
  uniq d m hm := by
    apply (cancel_epi (colimitHomology F n).inv).mp
    erw [Iso.inv_hom_id_assoc]
    apply colimit.hom_ext
    intro j
    have h := hm j
    change HomologicalComplex.homologyMap ((cocone F).ι.app j) n ≫ m = _ at h
    rw [homology_injection] at h
    have he := congrArg (fun t => (evaluationHomology F n j).inv ≫ t) h
    erw [Category.assoc (evaluationHomology F n j).hom,
      Iso.inv_hom_id_assoc (evaluationHomology F n j),
      Category.assoc (colimit.ι ((complex F).homology n) j)] at he
    erw [colimit.ι_desc]
    exact he
noncomputable instance homology_preserves (n : ℕ) :
    PreservesColimitsOfShape J (HomologicalComplex.homologyFunctor A c n) where
  preservesColimit {F} := preservesColimit_of_preserves_colimit_cocone (isColimit F) (homologyIsColimit F n)
end FilteredHomology

end

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits Opposite Simplicial
namespace FilteredHomology

variable {J : Type} [Category.{0} J]
noncomputable instance chain_preserves (Z : A) :
    PreservesColimitsOfShape J ((SSet.chainComplexFunctor A).obj Z) := by
  apply HomologicalComplex.preservesColimitsOfShape_of_eval
  intro n
  change PreservesColimitsOfShape J ((evaluation SimplexCategoryᵒᵖ (Type)).obj (op ⦋n⦌) ⋙ sigmaConst.obj Z)
  infer_instance
noncomputable instance sset_homology_preserves [IsFiltered J] (Z : A) (n:ℕ) :
    PreservesColimitsOfShape J (SSet.homologyFunctor Z n) := by
  change PreservesColimitsOfShape J (((SSet.chainComplexFunctor A).obj Z) ⋙
    HomologicalComplex.homologyFunctor A c n)
  infer_instance
end FilteredHomology
namespace SimpleAmenable.PolygonObject.LabelledStage.Stage
variable {a n : ℕ}

noncomputable def homologyIsColimit (q:ℕ) : IsColimit
    ((SSet.homologyFunctor (ModuleCat.of ℤ ℤ) q).mapCocone (nerveCocone (a:=a) (n:=n))) :=
  isColimitOfPreserves _ nerveIsColimit

noncomputable def barHomologyIsColimit (p q:ℕ) : IsColimit
    ((SSet.homologyFunctor (ModuleCat.of ℤ ℤ) q).mapCocone
      (barNerveCocone (a:=a) (n:=n) (I:=Fin (p+1)))) :=
  isColimitOfPreserves _ (barNerveIsColimit p)
end SimpleAmenable.PolygonObject.LabelledStage.Stage

end

open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits Opposite
namespace StageProductColimit

variable {C D E : Type} [Category.{0} C] [Category.{0} D] [Category.{0} E]
variable (κ : Type)
def powerMap (F : C ⥤ D) : (κ → C) ⥤ (κ → D) where
  obj U i := F.obj (U i)
  map f i := F.map (f i)
  map_id _ := by funext i; exact F.map_id _
  map_comp _ _ := by funext i; exact F.map_comp _ _
lemma powerMap_id : powerMap κ (𝟭 C)=𝟭 _ := rfl
lemma powerMap_comp (F : C ⥤ D) (G : D ⥤ E) :
    powerMap κ (F⋙G)=powerMap κ F ⋙ powerMap κ G := rfl
instance (F : C ⥤ D) [F.Faithful] : (powerMap κ F).Faithful where
  map_injective h := by funext i; exact F.map_injective (congrFun h i)
lemma powerMap_injective (F : C ⥤ D) (hF : Function.Injective F.obj) :
    Function.Injective (powerMap κ F).obj := by
  intro U V h; funext i; exact hF (congrFun h i)
end StageProductColimit
namespace SimpleAmenable.PolygonObject.LabelledStage.Stage
open StageProductColimit

variable {a n : ℕ} (κ : Type)
noncomputable def productStage : Stage a n ⥤ Cat.{0,0} where
  obj S := Cat.of (κ → S.Obj)
  map h := (powerMap κ (inclusion (leOfHom h))).toCatHom
  map_id S := by
    apply Cat.ext
    change powerMap κ (inclusion (le_refl S))=𝟭 _
    rw [inclusion_id]; rfl
  map_comp h k := by
    apply Cat.ext
    change powerMap κ (inclusion ((leOfHom h).trans (leOfHom k)))=
      powerMap κ (inclusion (leOfHom h)) ⋙ powerMap κ (inclusion (leOfHom k))
    rw [←powerMap_comp,←inclusion_comp]
noncomputable def productCocone : Cocone (productStage (a:=a) (n:=n) κ) where
  pt := Cat.of (κ → Labelled a n)
  ι := {
    app S := (powerMap κ S.forget).toCatHom
    naturality S T h := by
      apply Cat.ext
      change powerMap κ (inclusion (leOfHom h)) ⋙ powerMap κ T.forget=powerMap κ S.forget
      rw [←powerMap_comp,inclusion_forget] }
noncomputable def productNerveCocone : Cocone (productStage (a:=a) (n:=n) κ ⋙ nerveFunctor) :=
  nerveFunctor.mapCocone (productCocone κ)
lemma exists_lift_product [Fintype κ] {K : Type} [Category.{0} K] [Fintype K]
    [∀i j:K,Fintype (i ⟶ j)] (F : K ⥤ (κ → Labelled a n)) :
    ∃S : Stage a n,∃G : K ⥤ (κ → S.Obj),G ⋙ powerMap κ S.forget=F := by
  let τ := κ × (Σk:K,Σl:K,k ⟶ l)
  let U : κ × K → Labelled a n := fun t => F.obj t.2 t.1
  let src : τ → κ × K := fun t => (t.1,t.2.1)
  let dst : τ → κ × K := fun t => (t.1,t.2.2.1)
  let f : ∀t,U (src t) ⟶ U (dst t) := fun t => F.map t.2.2.2 t.1
  obtain ⟨S,hP,hL,hf⟩ := exists_lift_family U src dst f
  let G : K ⥤ (κ → S.Obj) := {
    obj k i := ⟨F.obj k i,hP (i,k),hL (i,k)⟩
    map {k l} g i := ⟨F.map g i,hf (i,⟨k,l,g⟩)⟩
    map_id k := by funext i; apply UniformObject.Hom.ext; exact congrFun (F.map_id k) i
    map_comp g h := by funext i; apply UniformObject.Hom.ext; exact congrFun (F.map_comp g h) i }
  exact ⟨S,G,rfl⟩
noncomputable def productNerveIsColimit [Fintype κ] :
    IsColimit (productNerveCocone (a:=a) (n:=n) κ) := by
  apply evaluationJointlyReflectsColimits
  intro p
  apply Types.FilteredColimit.isColimitOf'
  · intro x
    obtain ⟨S,G,h⟩ := exists_lift_product κ x
    exact ⟨S,G,h.symm⟩
  · intro S x y h
    have he : x=y := StageNerveColimit.comp_injective (powerMap κ S.forget)
      (powerMap_injective κ S.forget (forget_injective S)) h
    exact ⟨S,𝟙 S,congrArg _ he⟩
noncomputable def productHomologyIsColimit [Fintype κ] (q:ℕ) : IsColimit
    ((SSet.homologyFunctor (ModuleCat.of ℤ ℤ) q).mapCocone
      (productNerveCocone (a:=a) (n:=n) κ)) :=
  isColimitOfPreserves _ (productNerveIsColimit κ)
end SimpleAmenable.PolygonObject.LabelledStage.Stage

end OAI
