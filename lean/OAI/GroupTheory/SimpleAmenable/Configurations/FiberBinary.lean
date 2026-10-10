import Mathlib
import OAI.GroupTheory.SimpleAmenable.Configurations.StageBinary
import OAI.GroupTheory.SimpleAmenable.Homology.PiBinary

namespace OAI

open _root_.CategoryTheory _root_.OAI.CategoryTheory Limits MonoidalCategory Simplicial Opposite
namespace SimpleAmenable.PolygonTracks
open FreeChains ComponentTranslation ComponentStable

attribute [local instance 1200] Rep.hV2 Submodule.module Submodule.Quotient.module
lemma large_complement (a:ℕ) (p:Skeleton (PolygonObject a)) :
    ∃n,32 ≤ n ∧ ∃r,r*p=componentGenerator a^n := by
  obtain ⟨r,k,h⟩:=componentGenerator_cofinal a p
  refine ⟨32+k,by omega,componentGenerator a^32*r,?_⟩
  rw [mul_assoc,mul_comm r p,h,pow_add]
noncomputable def fiberToStage (a:ℕ) (p:Skeleton (PolygonObject a)) (n:ℕ)
    (r:Skeleton (PolygonObject a)) (h:r*p=componentGenerator a^n) :
    Fiber p ⥤ SingleObj (polygonFullGroup a n) :=
  ComponentTranslation.translate r p (componentGenerator a^n) h ⋙
    (standardFiberInclusion a n).asEquivalence.inverse
noncomputable def fiberToStageGlobal (a:ℕ) (p:Skeleton (PolygonObject a)) (n:ℕ)
    (r:Skeleton (PolygonObject a)) (h:r*p=componentGenerator a^n) :
    fiberToStage a p n r h ⋙ standardNerveInclusion a n ≅
      (property p).ι ⋙ tensorLeft (repr r) := by
  exact Functor.isoWhiskerRight
    (Functor.isoWhiskerLeft (ComponentTranslation.translate r p _ h)
      (standardFiberInclusion a n).asEquivalence.counitIso) (property (componentGenerator a^n)).ι
lemma fiber_value_mem (a:ℕ) (p q:Skeleton (PolygonObject a))
    (z:((nerve (Fiber p)⊗nerve (Fiber q)).homology Z 2:A)) :
    pullD (nerveMap (property p).ι) (nerveMap (property q).ι) 2 z ∈ mixedImage a := by
  obtain ⟨n,hn,r,hr⟩:=large_complement a p
  obtain ⟨m,hm,s,hs⟩:=large_complement a q
  let f:=fiberToStage a p n r hr
  let g:=fiberToStage a q m s hs
  have h : SSet.homologyMap (nerveMap f⊗ₘnerveMap g) Z 2 ≫
      pullD (nerveMap (standardNerveInclusion a n)) (nerveMap (standardNerveInclusion a m)) 2 =
        pullD (nerveMap (property p).ι) (nerveMap (property q).ι) 2 := by
    rw [pullD_comp]
    change pullD (nerveMap (fiberToStage a p n r hr ⋙ standardNerveInclusion a n))
      (nerveMap (fiberToStage a q m s hs ⋙ standardNerveInclusion a m)) 2 = _
    rw [pullD_congr (fiberToStageGlobal a p n r hr) (fiberToStageGlobal a q m s hs)]
    change pullD (nerveMap (property p).ι ≫ nerveMap (tensorLeft _))
      (nerveMap (property q).ι ≫ nerveMap (tensorLeft _)) 2 = _
    rw [pullD_left,pullD_right]
  have hv:=stage_value_mem a n m hn hm (SSet.homologyMap (nerveMap f⊗ₘnerveMap g) Z 2 z)
  have he:=congrArg (fun k=>k z) h
  exact he ▸ hv
lemma binaryD_quotient_zero (a:ℕ) : binaryD (C:=PolygonObject a) 2 ≫ ModuleCat.ofHom (mixedImage a).mkQ=0 := by
  apply (cancel_epi (SSet.homologyMap (PiSSet.binaryIso (fun _:Fin 2=>nerve (PolygonObject a))).hom Z 2)).mp
  apply (PiFiber.homologyIsColimit (PolygonObject a) (Fin 2) 2).hom_ext
  intro p
  change SSet.homologyMap (PiFiber.inclusion (PolygonObject a) (Fin 2) p.as) Z 2 ≫
    (SSet.homologyMap (PiSSet.binaryIso (fun _:Fin 2=>nerve (PolygonObject a))).hom Z 2 ≫
      (binaryD 2 ≫ ModuleCat.ofHom (mixedImage a).mkQ)) = _
  erw [←SSet.homologyMap_comp_assoc,PiFiber.binary_inclusion,SSet.homologyMap_comp_assoc]
  have hp : pullD (nerveMap (property (p.as 0)).ι) (nerveMap (property (p.as 1)).ι) 2 ≫
      ModuleCat.ofHom (mixedImage a).mkQ=0 := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    exact (Submodule.Quotient.mk_eq_zero (mixedImage a)).mpr (fiber_value_mem a (p.as 0) (p.as 1) z)
  change SSet.homologyMap _ Z 2 ≫ (pullD _ _ 2 ≫ ModuleCat.ofHom (mixedImage a).mkQ)=_
  erw [hp,comp_zero]
lemma mixedImage_finite (a:ℕ)
    [Module.Finite ℤ (groupHomology (Rep.trivial ℤ (polygonFullGroup a 32) ℤ) 1)] :
    Module.Finite ℤ (mixedImage a) := by
  let X:=nerve (SingleObj (polygonFullGroup a 32))
  have hf : ∀i,i<2 → Module.Finite ℤ (X.homology Z i:A) := by
    intro i hi
    interval_cases i
    · exact BarFinitePower.homology_zero_finite X
    · exact Module.Finite.equiv (GroupNerveCoordinates.homologyIso (polygonFullGroup a 32) 1).symm.toLinearEquiv
  have :=ConnectedProduct.finite_projection_kernel X X 2 hf hf
  exact Module.Finite.range _
end SimpleAmenable.PolygonTracks

end OAI
