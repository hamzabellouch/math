import Mathlib
import OAI.GroupTheory.SimpleAmenable.Homology.ExactShapeHomology

namespace OAI

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory Limits MonoidalCategory Simplicial Opposite
namespace PiSSet

variable {ι:Type} (C:ι→Type) [∀i,Category.{0} (C i)]
noncomputable def nervePiIso : nerve (∀i,C i) ≅ obj (fun i=>nerve (C i)) where
  hom := lift _ (fun i=>nerveMap (Pi.eval C i))
  inv := {app _ := ↾fun X=>Functor.pi' X
          naturality _ _ _ := by ext X; rfl}
  hom_inv_id := by ext p X; rfl
  inv_hom_id := by ext p X; rfl
end PiSSet
namespace ComponentTranslation
open FreeChains

variable {C:Type} [Groupoid.{0} C]
noncomputable def base (p:Skeleton C) : Fiber p := ⟨(fromSkeleton C).obj p,toSkeleton_fromSkeleton_obj p⟩
noncomputable def fiberIso (p:Skeleton C) (U V:Fiber p) : U≅V :=
  (property p).ι.preimageIso (Skeleton.isoOfEq (U.property.trans V.property.symm))
noncomputable instance fiber_nonempty (p:Skeleton C) : Nonempty (Fiber p) := ⟨base p⟩
instance fiber_nerve_connected (p:Skeleton C) : (nerve (Fiber p)).IsConnected where
  nonempty := ⟨nerveEquiv.symm (base p)⟩
  allEq x y := by
    obtain ⟨x,rfl⟩:=SSet.π₀.mk_surjective x
    obtain ⟨y,rfl⟩:=SSet.π₀.mk_surjective y
    have h:=SSet.π₀.sound (nerve.edgeMk (fiberIso p (nerveEquiv x) (nerveEquiv y)).hom)
    exact (congrArg SSet.π₀.mk (nerveEquiv.symm_apply_apply x)).symm.trans
      (h.trans (congrArg SSet.π₀.mk (nerveEquiv.symm_apply_apply y)))
end ComponentTranslation
namespace PiFiber
open ComponentTranslation FreeChains

variable (C:Type) [Groupoid.{0} C] (ι:Type)
noncomputable def prod : SSet := PiSSet.obj (fun _:ι=>nerve C)
noncomputable def piece (p:ι→Skeleton C) : SSet := PiSSet.obj (fun i=>nerve (Fiber (p i)))
noncomputable def diagram : Discrete (ι→Skeleton C) ⥤ SSet := Discrete.functor (piece C ι)
noncomputable def inclusion (p:ι→Skeleton C) : piece C ι p ⟶ prod C ι :=
  PiSSet.lift _ (fun i=>PiSSet.proj _ i ≫ nerveMap (property (p i)).ι)
noncomputable def cocone : Cocone (diagram C ι) := Cofan.mk (prod C ι) (inclusion C ι)
noncomputable def pointwiseIsColimit (n:ℕ) :
    IsColimit (((evaluation _ (Type)).obj (op ⦋n⦌)).mapCocone (cocone C ι)) := by
  let cf : Cofan (fun p:ι→Skeleton C=>∀i,ComposableArrows (Fiber (p i)) n) :=
    Cofan.mk (∀_:ι,ComposableArrows C n) (fun p=>↾fun s i=>s i ⋙ (property (p i)).ι)
  let s := (((evaluation _ (Type)).obj (op ⦋n⦌)).mapCocone (cocone C ι))
  let e : diagram C ι ⋙ (evaluation _ (Type)).obj (op ⦋n⦌) ≅
      Discrete.functor (fun p:ι→Skeleton C=>∀i,ComposableArrows (Fiber (p i)) n) :=
    Discrete.natIso (fun _=>Iso.refl _)
  let pointIso : s.pt ≅ cf.pt := Iso.refl _
  apply ColimitTransfer.ofIsos s cf e.hom pointIso.hom
    (fun _=>by simp [s,e,cf,cocone,pointIso]; rfl)
  apply Classical.choice
  rw [←cf.isColimit_cofanTypes_iff]
  apply CofanTypes.isColimit_mk
  · intro s
    exact ⟨fun i=>toSkeleton (s i).left,fun i=>ComponentCoproduct.lift C (s i),rfl⟩
  · intro p s t h
    funext i
    exact ComponentCoproduct.inclusion_injective C (p i) (congrFun h i)
  · intro p q s t h
    funext i
    have he:=CategoryTheory.Functor.congr_obj (congrFun h i) (0:Fin (n+1))
    exact (s i).left.property.symm.trans ((congrArg toSkeleton he).trans (t i).left.property)
noncomputable def isColimit : IsColimit (cocone C ι) :=
  evaluationJointlyReflectsColimits _ (fun n=>pointwiseIsColimit C ι n.unop.len)
noncomputable def homologyIsColimit (q:ℕ) :
    IsColimit ((SSet.homologyFunctor Z q).mapCocone (cocone C ι)) :=
  isColimitOfPreserves _ (isColimit C ι)
noncomputable def homologyIso (q:ℕ) : (prod C ι).homology Z q ≅
    ∐ (fun p:ι→Skeleton C=>(piece C ι p).homology Z q) :=
  (homologyIsColimit C ι q).coconePointUniqueUpToIso (colimit.isColimit _) ≪≫
    HasColimit.isoOfNatIso (Discrete.natIsoFunctor)
noncomputable def h1PieceIso (n:ℕ) (p:Fin n→Skeleton C) :
    (piece C (Fin n) p).homology Z 1 ≅ PiSSet.homologyPi (fun i=>nerve (Fiber (p i))) := by
  haveI := PiSSet.homologyProj_isIso n (fun i=>nerve (Fiber (p i))) (fun _=>inferInstance)
  exact asIso (X := (PiSSet.obj (fun i=>nerve (Fiber (p i)))).homology Z 1)
    (Y := PiSSet.homologyPi (fun i=>nerve (Fiber (p i))))
    (PiSSet.homologyProj n (fun i=>nerve (Fiber (p i))))
end PiFiber

end

end OAI
