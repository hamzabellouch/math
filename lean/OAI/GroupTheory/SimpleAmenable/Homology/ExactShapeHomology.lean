import Mathlib
import OAI.GroupTheory.SimpleAmenable.Homology.PiSSet

namespace OAI

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory Limits
namespace ExactShapeHomology

section

variable {J : Type} [Category.{0} J]
abbrev A := ModuleCat.{0} ℤ
abbrev c := ComplexShape.down ℕ
variable [HasExactColimitsOfShape J A]
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
    naturality _ _ f := by
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
omit [HasExactColimitsOfShape J A] in
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
         naturality i _ f := by
           have h := evaluationHomology_naturality F n f
           rw [←Iso.inv_comp_eq] at h
           rw [←h]
           simp only [Category.assoc,Functor.const_obj_map]
           erw [Iso.hom_inv_id_assoc,Category.comp_id]
           exact congrArg (fun t => (evaluationHomology F n i).inv ≫ t) (d.w f) }
noncomputable def homologyIsColimit (F : J ⥤ ChainComplex A ℕ) (n : ℕ) :
    IsColimit ((HomologicalComplex.homologyFunctor A c n).mapCocone (cocone F)) where
  desc d := (colimitHomology F n).hom ≫ colimit.desc _ (homologyCocone F n d)
  fac d j := by
    change HomologicalComplex.homologyMap ((cocone F).ι.app j) n ≫
      ((colimitHomology F n).hom ≫ colimit.desc _ (homologyCocone F n d)) = d.ι.app j
    rw [homology_injection]
    simp only [Category.assoc]
    erw [Iso.inv_hom_id_assoc,colimit.ι_desc]
    exact Iso.hom_inv_id_assoc _ _
  uniq d m hm := by
    change m = (colimitHomology F n).hom ≫ colimit.desc _ (homologyCocone F n d)
    apply (Iso.inv_comp_eq (colimitHomology F n)).mp
    apply colimit.hom_ext
    intro j
    erw [colimit.ι_desc]
    change colimit.ι ((complex F).homology n) j ≫ ((colimitHomology F n).inv ≫ m) =
      (evaluationHomology F n j).inv ≫ d.ι.app j
    apply (Iso.eq_inv_comp (evaluationHomology F n j)).mpr
    have h := hm j
    change HomologicalComplex.homologyMap ((cocone F).ι.app j) n ≫ m = _ at h
    rw [homology_injection] at h
    erw [Category.assoc,Category.assoc] at h
    exact h
noncomputable instance homology_preserves (n : ℕ) :
    PreservesColimitsOfShape J (HomologicalComplex.homologyFunctor A c n) where
  preservesColimit {F} := preservesColimit_of_preserves_colimit_cocone (isColimit F) (homologyIsColimit F n)
end
variable {J : Type} [Category.{0} J] [HasExactColimitsOfShape J A]
noncomputable instance sset_homology_preserves (Z:A) (n:ℕ) :
    PreservesColimitsOfShape J (SSet.homologyFunctor Z n) := by
  change PreservesColimitsOfShape J (((SSet.chainComplexFunctor A).obj Z) ⋙
    HomologicalComplex.homologyFunctor A c n)
  infer_instance
end ExactShapeHomology

end

open _root_.CategoryTheory _root_.OAI.CategoryTheory Limits Simplicial Opposite
namespace ComponentCoproduct
open ComponentTranslation FreeChains

variable (C:Type) [Groupoid.{0} C]
noncomputable def diagram : Discrete (Skeleton C) ⥤ SSet :=
  Discrete.functor (fun p=>nerve (Fiber p))
noncomputable def cocone : Cocone (diagram C) :=
  Cofan.mk (nerve C) (fun p=>nerveMap (property p).ι)
noncomputable def lift {n:ℕ} (s:ComposableArrows C n) :
    ComposableArrows (Fiber (toSkeleton s.left)) n :=
  (property (toSkeleton s.left)).lift s (fun i=>
    (congr_toSkeleton_of_iso (asIso (s.map (homOfLE (Fin.zero_le i))))).symm)
lemma lift_forget {n:ℕ} (s:ComposableArrows C n) :
    lift C s ⋙ (property (toSkeleton s.left)).ι=s := rfl
lemma inclusion_injective (p:Skeleton C) {n:ℕ} :
    Function.Injective (fun s:ComposableArrows (Fiber p) n=>s ⋙ (property p).ι) := by
  intro s t h
  have object_eq : ∀ index, s.obj index = t.obj index := by
    intro index
    apply ObjectProperty.FullSubcategory.ext
    exact CategoryTheory.Functor.congr_obj h index
  refine CategoryTheory.Functor.ext object_eq ?_
  intro source target arrow
  apply ObjectProperty.hom_ext
  simpa using CategoryTheory.Functor.congr_hom h arrow
noncomputable def pointwiseIsColimit (n:ℕ) :
    IsColimit (((evaluation _ (Type)).obj (op ⦋n⦌)).mapCocone (cocone C)) := by
  let cf : Cofan (fun p:Skeleton C=>ComposableArrows (Fiber p) n) :=
    Cofan.mk (ComposableArrows C n) (fun p=>↾fun s=>s ⋙ (property p).ι)
  let s := (((evaluation _ (Type)).obj (op ⦋n⦌)).mapCocone (cocone C))
  let e : diagram C ⋙ (evaluation _ (Type)).obj (op ⦋n⦌) ≅ Discrete.functor (fun p:Skeleton C=>ComposableArrows (Fiber p) n) := Discrete.natIso (fun _=>Iso.refl _)
  let pointIso : s.pt ≅ cf.pt := Iso.refl _
  apply ColimitTransfer.ofIsos s cf e.hom pointIso.hom (fun _=>by simp [s,e,cf,cocone,pointIso]; rfl)
  apply Classical.choice
  rw [←cf.isColimit_cofanTypes_iff]
  apply CofanTypes.isColimit_mk
  · intro s
    exact ⟨toSkeleton s.left,lift C s,rfl⟩
  · intro p; exact inclusion_injective C p
  · intro p q s t h
    have he := CategoryTheory.Functor.congr_obj h (0:Fin (n+1))
    exact s.left.property.symm.trans ((congrArg toSkeleton he).trans t.left.property)
noncomputable def isColimit : IsColimit (cocone C) :=
  evaluationJointlyReflectsColimits _ (fun n=>pointwiseIsColimit C n.unop.len)
noncomputable def homologyIsColimit (q:ℕ) :
    IsColimit ((SSet.homologyFunctor Z q).mapCocone (cocone C)) :=
  isColimitOfPreserves _ (isColimit C)
noncomputable def homologyIso (q:ℕ) :
    (nerve C).homology Z q ≅ ∐ (fun p:Skeleton C=>(nerve (Fiber p)).homology Z q) :=
  (homologyIsColimit C q).coconePointUniqueUpToIso (colimit.isColimit _) ≪≫
    HasColimit.isoOfNatIso (Discrete.natIsoFunctor)
end ComponentCoproduct

end OAI
