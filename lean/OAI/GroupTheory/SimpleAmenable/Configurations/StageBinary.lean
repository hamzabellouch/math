import Mathlib
import OAI.GroupTheory.SimpleAmenable.Configurations.PolygonFixedReturn
import OAI.GroupTheory.SimpleAmenable.Homology.ReducedNatural
import OAI.GroupTheory.SimpleAmenable.Homology.BinaryPullback

namespace OAI

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory Limits MonoidalCategory Simplicial Opposite
namespace GroupNerveCoordinates
variable (G:Type) [Monoid G]
instance zero_subsingleton : Subsingleton ((nerve (SingleObj G)).obj (op ⦋0⦌)) :=
  ⟨fun _ _=>nerveEquiv.injective (Subsingleton.elim _ _)⟩
instance connected : (nerve (SingleObj G)).IsConnected where
  nonempty:=⟨nerveEquiv.symm (SingleObj.star G)⟩
  allEq x y:=by
    obtain ⟨x,rfl⟩:=SSet.π₀.mk_surjective x
    obtain ⟨y,rfl⟩:=SSet.π₀.mk_surjective y
    congr 1
    exact Subsingleton.elim _ _
end GroupNerveCoordinates
namespace SimpleAmenable.PolygonTracks
open FreeChains ComponentTranslation ComponentStable

attribute [local instance 1200] Rep.hV2 Submodule.module
noncomputable def stageTranslate (a m:ℕ) (hm:32 ≤ m) :
    Fiber (componentGenerator a^32) ⥤ Fiber (componentGenerator a^m) :=
  ComponentTranslation.translate (componentGenerator a^(m-32)) _ _
    (by rw [←pow_add,Nat.sub_add_cancel hm])
lemma stageTranslate_H1_iso (a m:ℕ) (hm:32 ≤ m) :
    IsIso (SSet.homologyMap (nerveMap (stageTranslate a m hm)) Z 1) := by
  let F:=CofinalPowers.sequence (componentGenerator a) ⋙ homologyDiagram (C:=PolygonObject a) 1
  have h: F.IsEventuallyConstantFrom 32 := Functor.isEventuallyConstantFrom_of_succ F 32 (by
    intro n hn
    change IsIso ((homologyDiagram (C:=PolygonObject a) 1).map
      ((CofinalPowers.sequence (componentGenerator a)).map (homOfLE (Nat.le_succ n))))
    rw [component_sequence_succ]
    have successorIso := successor_H1_isIso a n hn
    exact component_successor_isIso a n 1)
  exact h (homOfLE hm)
noncomputable def fixedToStage (a m:ℕ) (hm:32 ≤ m) :
    SingleObj (polygonFullGroup a 32) ⥤ SingleObj (polygonFullGroup a m) :=
  standardFiberInclusion a 32 ⋙ stageTranslate a m hm ⋙ (standardFiberInclusion a m).asEquivalence.inverse
lemma fixedToStage_H1_iso (a m:ℕ) (hm:32 ≤ m) :
    IsIso (SSet.homologyMap (nerveMap (fixedToStage a m hm)) Z 1) := by
  have sourceInclusionIso := NerveHomotopy.homologyMap_isIso (standardFiberInclusion a 32) Z 1
  have targetInverseIso := NerveHomotopy.homologyMap_isIso (standardFiberInclusion a m).asEquivalence.inverse Z 1
  have translationIso := stageTranslate_H1_iso a m hm
  change IsIso (SSet.homologyMap
    (nerveMap (standardFiberInclusion a 32) ≫ nerveMap (stageTranslate a m hm) ≫
      nerveMap (standardFiberInclusion a m).asEquivalence.inverse) Z 1)
  simp only [SSet.homologyMap_comp]
  infer_instance
noncomputable def fixedToStageGlobal (a m:ℕ) (hm:32 ≤ m) :
    fixedToStage a m hm ⋙ standardNerveInclusion a m ≅
      standardNerveInclusion a 32 ⋙ tensorLeft (repr (componentGenerator a^(m-32))) := by
  let e := (standardFiberInclusion a m).asEquivalence
  let α := Functor.isoWhiskerLeft (standardFiberInclusion a 32 ⋙ stageTranslate a m hm) e.counitIso
  exact Functor.isoWhiskerRight α (property (componentGenerator a^m)).ι
lemma stage_pullD (a n m:ℕ) (hn:32 ≤ n) (hm:32 ≤ m) :
    SSet.homologyMap (nerveMap (fixedToStage a n hn)⊗ₘnerveMap (fixedToStage a m hm)) Z 2 ≫
      pullD (nerveMap (standardNerveInclusion a n)) (nerveMap (standardNerveInclusion a m)) 2 =
        pullD (nerveMap (standardNerveInclusion a 32)) (nerveMap (standardNerveInclusion a 32)) 2 := by
  rw [pullD_comp]
  change pullD (nerveMap (fixedToStage a n hn ⋙ standardNerveInclusion a n))
    (nerveMap (fixedToStage a m hm ⋙ standardNerveInclusion a m)) 2 = _
  rw [pullD_congr (fixedToStageGlobal a n hn) (fixedToStageGlobal a m hm)]
  change pullD (nerveMap (standardNerveInclusion a 32) ≫ nerveMap (tensorLeft _))
    (nerveMap (standardNerveInclusion a 32) ≫ nerveMap (tensorLeft _)) 2 = _
  rw [pullD_left,pullD_right]
noncomputable def mixedImage (a:ℕ) : Submodule ℤ (object (C:=PolygonObject a) 2) :=
  LinearMap.range ((pullD (nerveMap (standardNerveInclusion a 32))
    (nerveMap (standardNerveInclusion a 32)) 2).hom.comp
      (LinearMap.ker (ConnectedProduct.projection (nerve (SingleObj (polygonFullGroup a 32)))
        (nerve (SingleObj (polygonFullGroup a 32))) 2).hom).subtype)
lemma stage_value_mem (a n m:ℕ) (hn:32 ≤ n) (hm:32 ≤ m)
    (z:((nerve (SingleObj (polygonFullGroup a n))⊗nerve (SingleObj (polygonFullGroup a m))).homology Z 2:A)) :
    pullD (nerveMap (standardNerveInclusion a n)) (nerveMap (standardNerveInclusion a m)) 2 z ∈ mixedImage a := by
  obtain ⟨w,hw,he⟩:=pullD_kernel_value (nerveMap (standardNerveInclusion a n))
    (nerveMap (standardNerveInclusion a m)) (nerveEquiv.symm (SingleObj.star _))
      (nerveEquiv.symm (SingleObj.star _)) 2 (by decide) z
  have leftStageIso := fixedToStage_H1_iso a n hn
  have rightStageIso := fixedToStage_H1_iso a m hm
  obtain ⟨v,hv,hve⟩:=ConnectedProduct.kernel_map_surjective
    (nerveMap (fixedToStage a n hn)) (nerveMap (fixedToStage a m hm)) w hw
  refine ⟨⟨v,hv⟩,?_⟩
  have h:=congrArg (fun f=>f v) (stage_pullD a n m hn hm)
  change pullD (nerveMap (standardNerveInclusion a n)) (nerveMap (standardNerveInclusion a m)) 2
    (SSet.homologyMap (nerveMap (fixedToStage a n hn)⊗ₘnerveMap (fixedToStage a m hm)) Z 2 v)=_ at h
  rw [hve] at h
  exact h.symm.trans he
end SimpleAmenable.PolygonTracks

end

end OAI
