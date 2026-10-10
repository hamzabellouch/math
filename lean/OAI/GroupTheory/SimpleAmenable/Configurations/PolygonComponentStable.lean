import Mathlib
import OAI.GroupTheory.SimpleAmenable.PolygonGeometry.PolygonComponentCompletion
import OAI.GroupTheory.SimpleAmenable.Homology.PolygonStableHomology
import OAI.GroupTheory.SimpleAmenable.Homology.GroupoidComponentHomology
import OAI.GroupTheory.SimpleAmenable.Homology.ComponentStable

namespace OAI

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory Limits MonoidalCategory Simplicial Opposite
namespace SimpleAmenable.PolygonTracks
open FreeChains ComponentTranslation GroupoidComponentHomology

attribute [local instance 1200] Rep.hV2
noncomputable abbrev componentGenerator (a:ℕ) := PolygonObject.component (PolygonObject.standard a 1)
lemma componentGenerator_cofinal (a:ℕ) : ∀p:Skeleton (PolygonObject a),∃q n,p*q=componentGenerator a^n := by
  intro p
  let U:=ComponentTranslation.repr p
  refine ⟨PolygonObject.component (PolygonObject.complement U), U.tracks,?_⟩
  have h:=PolygonObject.component_complement U
  rw [PolygonObject.component_standard_pow] at h
  simpa only [U,PolygonObject.component,repr_component] using h
noncomputable def standardFiber (a n:ℕ) : Fiber (componentGenerator a^n) :=
  ⟨PolygonObject.standard a n,PolygonObject.component_standard_pow n⟩
noncomputable def standardNerveInclusion (a n:ℕ) :
    SingleObj (polygonFullGroup a n) ⥤ PolygonObject a :=
  (PolygonObject.standardAutEquiv a n).symm.toMonoidHom.toFunctor ⋙
    GroupoidComponentHomology.inclusion (PolygonObject.standard a n)
@[simp] lemma standardNerveInclusion_obj (a n:ℕ) (x:SingleObj (polygonFullGroup a n)) :
    (standardNerveInclusion a n).obj x=PolygonObject.standard a n := rfl
@[simp] lemma standardNerveInclusion_map (a n:ℕ) {x y:SingleObj (polygonFullGroup a n)} (f:x⟶y) :
    (standardNerveInclusion a n).map f=PolygonObject.fullGroupArrow f := rfl
noncomputable def standardFiberInclusion (a n:ℕ) :
    SingleObj (polygonFullGroup a n) ⥤ Fiber (componentGenerator a^n) :=
  (property (componentGenerator a^n)).lift (standardNerveInclusion a n)
    (fun _=>PolygonObject.component_standard_pow n)
noncomputable def standardHomologyIso (a n q:ℕ) :
    groupHomology (Rep.trivial ℤ (polygonFullGroup a n) ℤ) q ≅
      (nerve (Fiber (componentGenerator a^n))).homology Z q := by
  haveI:=TrivialHomology.isIso_equiv (PolygonObject.standardAutEquiv a n).symm q
  exact asIso (TrivialHomology.map (PolygonObject.standardAutEquiv a n).symm.toMonoidHom q) ≪≫
    fiberIsoHomology (standardFiber a n) q
end SimpleAmenable.PolygonTracks
namespace SimpleAmenable.PolygonObject
open SimpleAmenable SimpleAmenable.PolygonTracks

variable {a:ℕ}
lemma eqToHom_coord {U V:PolygonObject a} (h:U=V) (x:U.Point) :
    (((eqToHom h:U⟶V).toEquiv x).val.1.val,((eqToHom h:U⟶V).toEquiv x).val.2)=
      (x.val.1.val,x.val.2) := by subst V; rfl
lemma standardTensor_map (k n:ℕ) (f:polygonFullGroup a n) :
    (tensorLeft (standard a k)).map (fullGroupArrow f) ≫ eqToHom (sum_standard k n) =
      eqToHom (sum_standard k n) ≫ fullGroupArrow (stabilize a k n f) := by
  apply Arrow.ext
  apply Equiv.ext
  intro x
  apply Subtype.ext
  apply Prod.ext
  · apply Fin.ext
    obtain ⟨y,rfl⟩ := (sumPointEquiv (standard a k) (standard a n)).surjective x
    cases y with
    | inl y =>
      have hx:=congrArg (fun z : ℕ × GenericSquare a => z.1) (eqToHom_coord (sum_standard k n) (sumPointEquiv (standard a k) (standard a n) (.inl y)))
      simp only [arrow_comp_apply]
      change ((eqToHom (sum_standard k n)).toEquiv
        ((sumArrow (𝟙 _) (fullGroupArrow f)).toEquiv _)).val.1.val = _
      rw [sumArrow_inl,arrow_id_apply]
      rw [show ((eqToHom (sum_standard k n)).toEquiv _).val.1.val = y.val.1.val from hx]
      change _=((stabilize a k n f).val ((eqToHom (sum_standard k n)).toEquiv _).val).1.val
      have hp : ((eqToHom (sum_standard k n)).toEquiv
          (sumPointEquiv (standard a k) (standard a n) (.inl y))).val=(y.val.1.castAdd n,y.val.2) := by
        apply Prod.ext
        · apply Fin.ext; exact hx
        · exact congrArg (fun z : ℕ × GenericSquare a => z.2) (eqToHom_coord (sum_standard k n) _)
      erw [hp,stabilize_left]
      rfl
    | inr y =>
      have hp (z:(standard a n).Point) : ((eqToHom (sum_standard k n)).toEquiv
          (sumPointEquiv (standard a k) (standard a n) (.inr z))).val=(z.val.1.natAdd k,z.val.2) := by
        apply Prod.ext
        · apply Fin.ext; exact congrArg (fun z : ℕ × GenericSquare a => z.1) (eqToHom_coord (sum_standard k n) _)
        · exact congrArg (fun z : ℕ × GenericSquare a => z.2) (eqToHom_coord (sum_standard k n) _)
      simp only [arrow_comp_apply]
      change ((eqToHom (sum_standard k n)).toEquiv
        ((sumArrow (𝟙 _) (fullGroupArrow f)).toEquiv _)).val.1.val =
          ((stabilize a k n f).val ((eqToHom (sum_standard k n)).toEquiv _).val).1.val
      erw [sumArrow_inr,hp,hp,stabilize_right]
      rfl
  · obtain ⟨y,rfl⟩ := (sumPointEquiv (standard a k) (standard a n)).surjective x
    cases y with
    | inl y =>
      have hp : ((eqToHom (sum_standard k n)).toEquiv
          (sumPointEquiv (standard a k) (standard a n) (.inl y))).val=(y.val.1.castAdd n,y.val.2) := by
        apply Prod.ext
        · apply Fin.ext; exact congrArg (fun z : ℕ × GenericSquare a => z.1) (eqToHom_coord (sum_standard k n) _)
        · exact congrArg (fun z : ℕ × GenericSquare a => z.2) (eqToHom_coord (sum_standard k n) _)
      simp only [arrow_comp_apply]
      change ((eqToHom (sum_standard k n)).toEquiv
        ((sumArrow (𝟙 _) (fullGroupArrow f)).toEquiv _)).val.2 =
          ((stabilize a k n f).val ((eqToHom (sum_standard k n)).toEquiv _).val).2
      erw [sumArrow_inl,arrow_id_apply,hp,stabilize_left]
    | inr y =>
      have hp (z:(standard a n).Point) : ((eqToHom (sum_standard k n)).toEquiv
          (sumPointEquiv (standard a k) (standard a n) (.inr z))).val=(z.val.1.natAdd k,z.val.2) := by
        apply Prod.ext
        · apply Fin.ext; exact congrArg (fun z : ℕ × GenericSquare a => z.1) (eqToHom_coord (sum_standard k n) _)
        · exact congrArg (fun z : ℕ × GenericSquare a => z.2) (eqToHom_coord (sum_standard k n) _)
      simp only [arrow_comp_apply]
      change ((eqToHom (sum_standard k n)).toEquiv
        ((sumArrow (𝟙 _) (fullGroupArrow f)).toEquiv _)).val.2 =
          ((stabilize a k n f).val ((eqToHom (sum_standard k n)).toEquiv _).val).2
      erw [sumArrow_inr,hp,hp,stabilize_right]
      rfl
noncomputable def standardTensorIso (k n:ℕ) :
    standardNerveInclusion a n ⋙ tensorLeft (standard a k) ≅
      (stabilize a k n).toFunctor ⋙ standardNerveInclusion a (k+n) :=
  NatIso.ofComponents (fun _=>eqToIso (sum_standard k n)) (by
    intro x y f
    exact standardTensor_map k n f)
noncomputable def standardCastIso {m n:ℕ} (h:m=n) : standardNerveInclusion a m ≅
    (castFull a h).toMonoidHom.toFunctor ⋙ standardNerveInclusion a n := by
  subst n
  exact NatIso.ofComponents (fun _=>Iso.refl _) (by intro x y f; simp; rfl)
noncomputable def standardSuccessorIso (n:ℕ) :
    standardNerveInclusion a n ⋙ tensorLeft (standard a 1) ≅
      (successorStabilize a n).toFunctor ⋙ standardNerveInclusion a (n+1) :=
  standardTensorIso 1 n ≪≫
    Functor.isoWhiskerLeft (stabilize a 1 n).toFunctor (standardCastIso (Nat.add_comm 1 n)) ≪≫
      (Functor.associator _ _ _).symm
end SimpleAmenable.PolygonObject
namespace SimpleAmenable.PolygonTracks
open FreeChains ComponentTranslation GroupoidComponentHomology

instance standardFiberInclusion_faithful (a n:ℕ) : (standardFiberInclusion a n).Faithful where
  map_injective h := PolygonObject.fullGroupArrow_injective
    (congrArg (fun f : (standardFiberInclusion a n).obj _ ⟶ (standardFiberInclusion a n).obj _ => f.hom) h)
noncomputable instance standardFiberInclusion_full (a n:ℕ) : (standardFiberInclusion a n).Full where
  map_surjective f := ⟨PolygonObject.fullGroupOfArrow f.hom,by
    apply ObjectProperty.hom_ext
    exact PolygonObject.arrow_fullGroup f.hom⟩
instance standardFiberInclusion_essSurj (a n:ℕ) : (standardFiberInclusion a n).EssSurj where
  mem_essImage V := ⟨SingleObj.star _,⟨fiberIso _ (standardFiber a n) V⟩⟩
noncomputable instance standardFiberInclusion_isEquivalence (a n:ℕ) :
    (standardFiberInclusion a n).IsEquivalence := ⟨inferInstance,inferInstance,inferInstance⟩
noncomputable def representativeGeneratorIso (a:ℕ) :
    repr (componentGenerator a) ≅ PolygonObject.standard a 1 := Skeleton.isoOfEq (repr_component _)
noncomputable def representativeSuccessorIso (a n:ℕ) :
    standardNerveInclusion a n ⋙ tensorLeft (repr (componentGenerator a)) ≅
      (successorStabilize a n).toFunctor ⋙ standardNerveInclusion a (n+1) :=
  Functor.isoWhiskerLeft (standardNerveInclusion a n)
    ((tensoringLeft (PolygonObject a)).mapIso (representativeGeneratorIso a)) ≪≫
      PolygonObject.standardSuccessorIso n
noncomputable def fiberSuccessorIso (a n:ℕ) :
    standardFiberInclusion a n ⋙
      ComponentTranslation.translate (componentGenerator a) (componentGenerator a^n) (componentGenerator a^(n+1)) (pow_succ' _ _).symm ≅
        (successorStabilize a n).toFunctor ⋙ standardFiberInclusion a (n+1) :=
  NatIso.ofComponents (fun x=>ObjectProperty.isoMk _ ((representativeSuccessorIso a n).app x)) (by
    intro x y f
    apply ObjectProperty.hom_ext
    exact (representativeSuccessorIso a n).hom.naturality f)
lemma component_successor_isIso (a n q:ℕ) [IsIso (TrivialHomology.map (successorStabilize a n) q)] :
    IsIso (SSet.homologyMap (nerveMap
      (ComponentTranslation.translate (componentGenerator a) (componentGenerator a^n) (componentGenerator a^(n+1)) (pow_succ' _ _).symm)) Z q) := by
  have sourceInclusionIso := NerveHomotopy.homologyMap_isIso (standardFiberInclusion a n) Z q
  have targetInclusionIso := NerveHomotopy.homologyMap_isIso (standardFiberInclusion a (n+1)) Z q
  have hg:=GroupNerveCoordinates.homologyIso_natural (successorStabilize a n) q
  have successorIso : IsIso (SSet.homologyMap (nerveMap (successorStabilize a n).toFunctor) Z q) := by
    have successorCompositeIso : IsIso (SSet.homologyMap (nerveMap (successorStabilize a n).toFunctor) Z q ≫
      (GroupNerveCoordinates.homologyIso (polygonFullGroup a (n+1)) q).hom) := by rw [hg]; infer_instance
    exact (isIso_comp_right_iff _ (GroupNerveCoordinates.homologyIso (polygonFullGroup a (n+1)) q).hom).mp inferInstance
  have h:=(NerveHomotopy.ofNatTrans (fiberSuccessorIso a n).hom).congr_homologyMap Z q
  rw [ComponentStable.map_comp,ComponentStable.map_comp] at h
  have inclusionCompositeIso : IsIso (SSet.homologyMap (nerveMap (standardFiberInclusion a n)) Z q ≫
    SSet.homologyMap (nerveMap
      (ComponentTranslation.translate (componentGenerator a) (componentGenerator a^n) (componentGenerator a^(n+1)) (pow_succ' _ _).symm)) Z q) := by
    rw [h]
    infer_instance
  exact (isIso_comp_left_iff (SSet.homologyMap (nerveMap (standardFiberInclusion a n)) Z q) _).mp inferInstance
end SimpleAmenable.PolygonTracks

end

end OAI
