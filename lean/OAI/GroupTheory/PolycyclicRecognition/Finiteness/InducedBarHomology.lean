import OAI.GroupTheory.PolycyclicRecognition.Algebra.InducedBarTranslation
import OAI.GroupTheory.PolycyclicRecognition.Finiteness.NormalHomologyAction

namespace OAI

/-! # Translation on induced bar homology is actual conjugation -/

noncomputable section
namespace PolycyclicRecognition
open CategoryTheory HomologicalComplex
open scoped TensorProduct
attribute [local instance 2000] Rep.hV2 Rep.instLinear
attribute [local instance 2100] Linear.homModule
attribute [local instance 2200] TensorProduct.instModule
attribute [local instance 2300] Representation.Coinvariants.instModule Pi.Function.module
variable {G : Type} [Group G] (N : Subgroup G) [N.Normal] (A : Rep ℤ G)

omit [N.Normal] in
theorem inducedTensorRightIso_inv_mk (B : Rep ℤ N) (a : A) (b : B) :
    (inducedTensorRightIso N A B).inv
        (Rep.coinvariantsTensorMk (Rep.res N.subtype A) B a b) =
      Rep.coinvariantsTensorMk A (Rep.ind N.subtype B) a
        (Representation.IndV.mk N.subtype B.ρ 1 b) := by
  apply (ModuleCat.mono_iff_injective (inducedTensorRightIso N A B).hom).mp inferInstance
  rw [← ModuleCat.comp_apply, Iso.inv_hom_id, ModuleCat.id_apply,
    inducedTensorRightIso_mk, map_one, Module.End.one_apply]

def inducedBarChainsIso [DecidableEq N] :
    groupHomology.inhomogeneousChains (Rep.res N.subtype A) ≅
      (normalInducedResolution ℤ N (Rep.barResolution ℤ N)).complex.coinvariantsTensorObj A :=
  groupHomology.inhomogeneousChainsIso (Rep.res N.subtype A) ≪≫
    (inducedResolutionTensorIso N A (Rep.barResolution ℤ N)).symm

theorem inducedBarChainsIso_translation [DecidableEq N] (t : G) :
    groupHomology.chainsMap (MulAut.conjNormal (H := N) t⁻¹).toMonoidHom
        (normalHomologyCoefficient ℤ N A t⁻¹) ≫ (inducedBarChainsIso N A).hom =
      (inducedBarChainsIso N A).hom ≫
        (((Rep.coinvariantsTensor ℤ G).obj A).mapHomologicalComplex (ComplexShape.down ℕ)).map
          (inducedBarTranslation N t) := by
  apply (cancel_mono (inducedResolutionTensorIso N A (Rep.barResolution ℤ N)).hom).mp
  apply HomologicalComplex.Hom.ext
  funext i
  apply ModuleCat.hom_ext
  apply Finsupp.lhom_ext'
  intro x
  apply LinearMap.ext
  intro v
  change (inducedTensorRightIso N A (Rep.free ℤ N (Fin i → N))).hom
      ((inducedTensorRightIso N A (Rep.free ℤ N (Fin i → N))).inv
        (Rep.finsuppToCoinvariantsTensorFree (Rep.res N.subtype A) (Fin i → N)
          ((groupHomology.chainsMap (MulAut.conjNormal (H := N) t⁻¹).toMonoidHom
            (normalHomologyCoefficient ℤ N A t⁻¹)).f i (Finsupp.single x v)))) =
    (inducedTensorRightIso N A (Rep.free ℤ N (Fin i → N))).hom
      ((((Rep.coinvariantsTensor ℤ G).obj A).map ((inducedBarTranslation N t).f i))
        ((inducedTensorRightIso N A (Rep.free ℤ N (Fin i → N))).inv
          (Rep.finsuppToCoinvariantsTensorFree (Rep.res N.subtype A) (Fin i → N)
            (Finsupp.single x v))))
  rw [← ModuleCat.comp_apply, Iso.inv_hom_id, ModuleCat.id_apply,
    groupHomology.chainsMap_f_single, Rep.finsuppToCoinvariantsTensorFree_single,
    Rep.finsuppToCoinvariantsTensorFree_single]
  change Rep.coinvariantsTensorMk (Rep.res N.subtype A) (Rep.free ℤ N (Fin i → N))
      (A.ρ t⁻¹ v) (Finsupp.single ((MulAut.conjNormal (H := N) t⁻¹) ∘ x)
        (MonoidAlgebra.single 1 1)) =
    (inducedTensorRightIso N A (Rep.free ℤ N (Fin i → N))).hom
      ((((Rep.coinvariantsTensor ℤ G).obj A).map ((inducedBarTranslation N t).f i))
        ((inducedTensorRightIso N A (Rep.free ℤ N (Fin i → N))).inv
          (Rep.coinvariantsTensorMk (Rep.res N.subtype A) (Rep.free ℤ N (Fin i → N)) v
            (Finsupp.single x (MonoidAlgebra.single 1 1)))))
  rw [inducedTensorRightIso_inv_mk]
  change _ = (inducedTensorRightIso N A (Rep.free ℤ N (Fin i → N))).hom
    (Rep.coinvariantsTensorMk A (Rep.ind N.subtype (Rep.free ℤ N (Fin i → N))) v
      ((inducedSemilinearMap ℤ N t _ _
        (barAutomorphismFreeMap (MulAut.conjNormal (H := N) t⁻¹) i)).hom
        (Representation.IndV.mk N.subtype (Rep.free ℤ N (Fin i → N)).ρ 1
          (Finsupp.single x (MonoidAlgebra.single 1 1)))))
  rw [inducedSemilinearMap_mk, mul_one, barAutomorphismFreeMap_single, map_one,
    inducedTensorRightIso_mk]

def inducedBarHomologyIso [DecidableEq N] (d : ℕ) :
    ((normalInducedResolution ℤ N (Rep.barResolution ℤ N)).complex.coinvariantsTensorObj A).homology d ≅
      groupHomology (Rep.res N.subtype A) d :=
  (HomologicalComplex.homologyFunctor (ModuleCat ℤ) (ComplexShape.down ℕ) d).mapIso
    (inducedBarChainsIso N A).symm

theorem inducedBarHomologyIso_translation [DecidableEq N] (t : G) (d : ℕ) :
    HomologicalComplex.homologyMap
        ((((Rep.coinvariantsTensor ℤ G).obj A).mapHomologicalComplex (ComplexShape.down ℕ)).map
          (inducedBarTranslation N t)) d ≫ (inducedBarHomologyIso N A d).hom =
      (inducedBarHomologyIso N A d).hom ≫ normalHomologyMap ℤ N A d t⁻¹ := by
  let C := inducedBarChainsIso N A
  let T := (((Rep.coinvariantsTensor ℤ G).obj A).mapHomologicalComplex (ComplexShape.down ℕ)).map
    (inducedBarTranslation N t)
  let f := groupHomology.chainsMap (MulAut.conjNormal (H := N) t⁻¹).toMonoidHom
    (normalHomologyCoefficient ℤ N A t⁻¹)
  have hc : f ≫ C.hom = C.hom ≫ T := inducedBarChainsIso_translation N A t
  have h : T ≫ C.inv = C.inv ≫ f := by
    apply (cancel_epi C.hom).mp
    rw [← Category.assoc]
    rw [← hc]
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id, Iso.hom_inv_id_assoc]
  change HomologicalComplex.homologyMap T d ≫ HomologicalComplex.homologyMap C.inv d =
    HomologicalComplex.homologyMap C.inv d ≫ HomologicalComplex.homologyMap f d
  simpa only [HomologicalComplex.homologyMap_comp] using
    congrArg (fun u => HomologicalComplex.homologyMap u d) h

end PolycyclicRecognition

end

end OAI
