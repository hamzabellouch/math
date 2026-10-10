import Mathlib
import OAI.GroupTheory.SimpleAmenable.Homology.ComponentStable

namespace OAI

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory Limits MonoidalCategory Simplicial Opposite
namespace NerveProduct
open FreeChains

variable (C D:Type) [Category.{0} C] [Category.{0} D]
noncomputable def iso : nerve (C×D) ≅ nerve C⊗nerve D where
  hom := {app _:=↾fun F=>(F⋙CategoryTheory.Prod.fst C D,F⋙CategoryTheory.Prod.snd C D)
          naturality _ _ _:=rfl}
  inv := {app _:=↾fun F=>F.1.prod' F.2
          naturality _ _ _:=rfl}
  hom_inv_id := by ext p F; rfl
  inv_hom_id := by ext p F <;> rfl
variable {C D} {C' D':Type} [Category.{0} C'] [Category.{0} D']
@[reassoc] lemma natural (f:C⥤C') (g:D⥤D') :
    nerveMap (f.prod g) ≫ (iso C' D').hom=(iso C D).hom ≫ (nerveMap f⊗ₘnerveMap g) := rfl
@[simp] lemma fst : (iso C D).hom ≫ CartesianMonoidalCategory.fst _ _=nerveMap (CategoryTheory.Prod.fst C D) := rfl
@[simp] lemma snd : (iso C D).hom ≫ CartesianMonoidalCategory.snd _ _=nerveMap (CategoryTheory.Prod.snd C D) := rfl
end NerveProduct
namespace ComponentStable
open FreeChains ComponentTranslation

variable {C:Type} [Groupoid.{0} C] [MonoidalCategory C] [SymmetricCategory C]
noncomputable def reprObjectIso (U:C) : repr (toSkeleton U) ≅ U := Skeleton.isoOfEq (repr_component _)
omit [SymmetricCategory C] in
lemma tensorLeft_stable (U:C) (q:ℕ) :
    SSet.homologyMap (nerveMap (tensorLeft U)) Z q ≫ toStable q=toStable (C:=C) q := by
  apply (ComponentCoproduct.homologyIsColimit C q).hom_ext
  intro p
  change inclusion p.as q ≫ (SSet.homologyMap (nerveMap (tensorLeft U)) Z q ≫ toStable q)=inclusion p.as q ≫ toStable q
  let e : (property p.as).ι ⋙ tensorLeft U ≅
      translate (toSkeleton U) p.as (toSkeleton U*p.as) rfl ⋙ (property (toSkeleton U*p.as)).ι :=
    (Functor.isoWhiskerLeft (property p.as).ι ((tensoringLeft C).mapIso (reprObjectIso U))).symm
  have h:=(NerveHomotopy.ofNatTrans e.hom).congr_homologyMap Z q
  change SSet.homologyMap (nerveMap (property p.as).ι ≫ nerveMap (tensorLeft U)) Z q =
    SSet.homologyMap (nerveMap (translate (toSkeleton U) p.as (toSkeleton U*p.as) rfl) ≫ nerveMap (property (toSkeleton U*p.as)).ι) Z q at h
  rw [SSet.homologyMap_comp,SSet.homologyMap_comp] at h
  change inclusion p.as q ≫ (SSet.homologyMap (nerveMap (tensorLeft U)) Z q ≫ toStable q)=_
  rw [←Category.assoc]
  change (SSet.homologyMap (nerveMap (property p.as).ι) Z q ≫ SSet.homologyMap (nerveMap (tensorLeft U)) Z q) ≫ toStable q = _
  rw [h,Category.assoc]
  exact translate_toStable _ _ _ rfl q
lemma tensorRight_stable (U:C) (q:ℕ) :
    SSet.homologyMap (nerveMap (tensorRight U)) Z q ≫ toStable q=toStable (C:=C) q := by
  have h:=(NerveHomotopy.ofNatTrans (BraidedCategory.tensorLeftIsoTensorRight U).hom).congr_homologyMap Z q
  rw [←h,tensorLeft_stable]
noncomputable def tensorFunctor : C×C ⥤ C where
  obj X:=X.1⊗X.2
  map f:=f.1⊗ₘf.2
  map_id _:=by simp
  map_comp _ _:=by simp [tensorHom_comp_tensorHom]
noncomputable def multiplication : nerve C⊗nerve C ⟶ nerve C :=
  (NerveProduct.iso C C).inv ≫ nerveMap tensorFunctor
noncomputable def binaryD (q:ℕ) : (nerve C⊗nerve C).homology Z q ⟶ object (C:=C) q :=
  (SSet.homologyMap (CartesianMonoidalCategory.fst _ _) Z q +
    SSet.homologyMap (CartesianMonoidalCategory.snd _ _) Z q -
      SSet.homologyMap multiplication Z q) ≫ toStable q
noncomputable def leftTensorIso (U:C) :
    ((tensorLeft U).prod (𝟭 C)) ⋙ tensorFunctor ≅ tensorFunctor ⋙ tensorLeft U :=
  NatIso.ofComponents (fun X=>α_ U X.1 X.2) (by
    intro X Y f
    change ((U ◁ f.1)⊗ₘf.2) ≫ (α_ U Y.1 Y.2).hom = (α_ U X.1 X.2).hom ≫ (U ◁ (f.1⊗ₘf.2))
    simp [←id_tensorHom])
noncomputable def rightTensorIso (U:C) :
    ((𝟭 C).prod (tensorRight U)) ⋙ tensorFunctor ≅ tensorFunctor ⋙ tensorRight U :=
  NatIso.ofComponents (fun X=>(α_ X.1 X.2 U).symm) (by
    intro X Y f
    change (f.1⊗ₘ(f.2 ▷ U)) ≫ (α_ Y.1 Y.2 U).inv = (α_ X.1 X.2 U).inv ≫ ((f.1⊗ₘf.2) ▷ U)
    simp [←tensorHom_id])
omit [SymmetricCategory C] in
@[reassoc] lemma multiplication_left (U:C) (q:ℕ) :
    SSet.homologyMap (nerveMap (tensorLeft U)⊗ₘ𝟙 (nerve C)) Z q ≫
      SSet.homologyMap multiplication Z q ≫ toStable q =
        SSet.homologyMap (multiplication (C:=C)) Z q ≫ toStable q := by
  apply (cancel_epi (SSet.homologyMap (NerveProduct.iso C C).hom Z q)).mp
  rw [←SSet.homologyMap_comp_assoc]
  have he : (NerveProduct.iso C C).hom ≫ (nerveMap (tensorLeft U)⊗ₘ𝟙 (nerve C)) =
      nerveMap ((tensorLeft U).prod (𝟭 C)) ≫ (NerveProduct.iso C C).hom := rfl
  have hm : (NerveProduct.iso C C).hom ≫ multiplication=nerveMap tensorFunctor := by simp [multiplication]
  rw [he,SSet.homologyMap_comp_assoc]
  rw [←SSet.homologyMap_comp_assoc (f:=(NerveProduct.iso C C).hom) (g:=multiplication),hm]
  rw [←SSet.homologyMap_comp_assoc]
  have h:=(NerveHomotopy.ofNatTrans (leftTensorIso U).hom).congr_homologyMap Z q
  change SSet.homologyMap (nerveMap (((tensorLeft U).prod (𝟭 C)) ⋙ tensorFunctor)) Z q ≫ toStable q = _
  rw [h,map_comp,Category.assoc,tensorLeft_stable]
@[reassoc] lemma multiplication_right (U:C) (q:ℕ) :
    SSet.homologyMap (𝟙 (nerve C)⊗ₘnerveMap (tensorRight U)) Z q ≫
      SSet.homologyMap multiplication Z q ≫ toStable q =
        SSet.homologyMap (multiplication (C:=C)) Z q ≫ toStable q := by
  apply (cancel_epi (SSet.homologyMap (NerveProduct.iso C C).hom Z q)).mp
  rw [←SSet.homologyMap_comp_assoc]
  have he : (NerveProduct.iso C C).hom ≫ (𝟙 (nerve C)⊗ₘnerveMap (tensorRight U)) =
      nerveMap ((𝟭 C).prod (tensorRight U)) ≫ (NerveProduct.iso C C).hom := rfl
  have hm : (NerveProduct.iso C C).hom ≫ multiplication=nerveMap tensorFunctor := by simp [multiplication]
  rw [he,SSet.homologyMap_comp_assoc]
  rw [←SSet.homologyMap_comp_assoc (f:=(NerveProduct.iso C C).hom) (g:=multiplication),hm]
  rw [←SSet.homologyMap_comp_assoc]
  have h:=(NerveHomotopy.ofNatTrans (rightTensorIso U).hom).congr_homologyMap Z q
  change SSet.homologyMap (nerveMap (((𝟭 C).prod (tensorRight U)) ⋙ tensorFunctor)) Z q ≫ toStable q = _
  rw [h,map_comp,Category.assoc,tensorRight_stable]
end ComponentStable

end

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory Limits MonoidalCategory Simplicial Opposite
namespace NerveProduct
open FreeChains

variable {C D E F:Type} [Category.{0} C] [Category.{0} D] [Category.{0} E] [Category.{0} F]
lemma homology_congr {f f':C⥤E} {g g':D⥤F} (α:f≅f') (β:g≅g') (q:ℕ) :
    SSet.homologyMap (nerveMap f⊗ₘnerveMap g) Z q=SSet.homologyMap (nerveMap f'⊗ₘnerveMap g') Z q := by
  apply (cancel_epi (SSet.homologyMap (iso C D).hom Z q)).mp
  rw [←SSet.homologyMap_comp,←natural,←SSet.homologyMap_comp,←natural,
    SSet.homologyMap_comp,SSet.homologyMap_comp]
  rw [(NerveHomotopy.ofNatTrans (NatIso.prod α β).hom).congr_homologyMap Z q]
end NerveProduct
namespace ComponentStable
open FreeChains ComponentTranslation ConnectedProduct

variable {C:Type} [Groupoid.{0} C] [MonoidalCategory C] [SymmetricCategory C]
omit [SymmetricCategory C] in
@[reassoc] lemma binaryD_left (U:C) (q:ℕ) :
    SSet.homologyMap (nerveMap (tensorLeft U)⊗ₘ𝟙 (nerve C)) Z q ≫ binaryD q=binaryD (C:=C) q := by
  let f:=nerveMap (tensorLeft U)⊗ₘ𝟙 (nerve C)
  have hf : f≫CartesianMonoidalCategory.fst _ _=CartesianMonoidalCategory.fst _ _≫nerveMap (tensorLeft U) := rfl
  have hg : f≫CartesianMonoidalCategory.snd _ _=CartesianMonoidalCategory.snd _ _ := rfl
  simp only [binaryD,Preadditive.comp_add,Preadditive.comp_sub,Preadditive.add_comp,Preadditive.sub_comp]
  rw [multiplication_left,←SSet.homologyMap_comp_assoc,hf,SSet.homologyMap_comp_assoc,tensorLeft_stable,
    ←SSet.homologyMap_comp_assoc,hg]
@[reassoc] lemma binaryD_right (U:C) (q:ℕ) :
    SSet.homologyMap (𝟙 (nerve C)⊗ₘnerveMap (tensorRight U)) Z q ≫ binaryD q=binaryD (C:=C) q := by
  let f:=𝟙 (nerve C)⊗ₘnerveMap (tensorRight U)
  have hf : f≫CartesianMonoidalCategory.fst _ _=CartesianMonoidalCategory.fst _ _ := rfl
  have hg : f≫CartesianMonoidalCategory.snd _ _=CartesianMonoidalCategory.snd _ _≫nerveMap (tensorRight U) := rfl
  simp only [binaryD,Preadditive.comp_add,Preadditive.comp_sub,Preadditive.add_comp,Preadditive.sub_comp]
  rw [multiplication_right,←SSet.homologyMap_comp_assoc,hf,←SSet.homologyMap_comp_assoc,hg,
    SSet.homologyMap_comp_assoc,tensorRight_stable]
@[reassoc] lemma binaryD_second_left (U:C) (q:ℕ) :
    SSet.homologyMap (𝟙 (nerve C)⊗ₘnerveMap (tensorLeft U)) Z q ≫ binaryD q=binaryD (C:=C) q := by
  have h:=NerveProduct.homology_congr (Iso.refl (𝟭 C)) (BraidedCategory.tensorLeftIsoTensorRight U) q
  change SSet.homologyMap (𝟙 (nerve C)⊗ₘnerveMap (tensorLeft U)) Z q =
    SSet.homologyMap (𝟙 (nerve C)⊗ₘnerveMap (tensorRight U)) Z q at h
  rw [h,binaryD_right]
omit [SymmetricCategory C] in
lemma pairLeft_multiplication (U:C) :
    pairLeft (nerve C) (nerve C) (nerveEquiv.symm U) ≫ multiplication=nerveMap (tensorRight U) := by
  apply NatTrans.ext; funext p; apply ConcreteCategory.hom_ext; intro F
  apply CategoryTheory.Functor.ext
  · intro x y f
    change (F.map f ⊗ₘ 𝟙 U) = 𝟙 _ ≫ (F.map f ▷ U) ≫ 𝟙 _
    simp
  · intro x; rfl
omit [SymmetricCategory C] in
lemma pairRight_multiplication (U:C) :
    pairRight (nerve C) (nerve C) (nerveEquiv.symm U) ≫ multiplication=nerveMap (tensorLeft U) := by
  apply NatTrans.ext; funext p; apply ConcreteCategory.hom_ext; intro F
  apply CategoryTheory.Functor.ext
  · intro x y f
    change (𝟙 U ⊗ₘ F.map f) = 𝟙 _ ≫ (U ◁ F.map f) ≫ 𝟙 _
    simp
  · intro x; rfl
@[reassoc] lemma pairLeft_binaryD (v:(nerve C).obj (op ⦋0⦌)) (q:ℕ) (hq:q≠0) :
    SSet.homologyMap (pairLeft (nerve C) (nerve C) v) Z q ≫ binaryD q=0 := by
  obtain ⟨U,rfl⟩:=nerveEquiv.symm.surjective v
  have constant_zero : SSet.homologyMap (SSet.const (nerveEquiv.symm U) : nerve C ⟶ nerve C) Z q = 0 :=
    const_homology_zero _ q hq
  simp only [binaryD,Preadditive.comp_add,Preadditive.comp_sub,Preadditive.add_comp,Preadditive.sub_comp]
  rw [←SSet.homologyMap_comp_assoc,←SSet.homologyMap_comp_assoc,←SSet.homologyMap_comp_assoc,
    pairLeft_multiplication]
  simp only [pairLeft,CartesianMonoidalCategory.lift_fst,CartesianMonoidalCategory.lift_snd,
    SSet.homologyMap_id,constant_zero,Category.id_comp,zero_comp,add_zero,tensorRight_stable,sub_self]
omit [SymmetricCategory C] in
@[reassoc] lemma pairRight_binaryD (v:(nerve C).obj (op ⦋0⦌)) (q:ℕ) (hq:q≠0) :
    SSet.homologyMap (pairRight (nerve C) (nerve C) v) Z q ≫ binaryD q=0 := by
  obtain ⟨U,rfl⟩:=nerveEquiv.symm.surjective v
  have constant_zero : SSet.homologyMap (SSet.const (nerveEquiv.symm U) : nerve C ⟶ nerve C) Z q = 0 :=
    const_homology_zero _ q hq
  simp only [binaryD,Preadditive.comp_add,Preadditive.comp_sub,Preadditive.add_comp,Preadditive.sub_comp]
  rw [←SSet.homologyMap_comp_assoc,←SSet.homologyMap_comp_assoc,←SSet.homologyMap_comp_assoc,
    pairRight_multiplication]
  simp only [pairRight,CartesianMonoidalCategory.lift_fst,CartesianMonoidalCategory.lift_snd,
    SSet.homologyMap_id,constant_zero,Category.id_comp,zero_comp,zero_add,tensorLeft_stable,sub_self]
end ComponentStable

end

end OAI
