import OAI.GroupTheory.PolycyclicRecognition.Finiteness.SubgroupBarResolution
import OAI.GroupTheory.PolycyclicRecognition.Algebra.FiniteIndexTrace
import OAI.GroupTheory.PolycyclicRecognition.Finiteness.HomologyClassExhaustion

namespace OAI

/-! # The Shapiro comparison associated to subgroup inclusion -/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory HomologicalComplex Rep
attribute [local instance 2000] Rep.hV2 Rep.instLinear
attribute [local instance 2100] Linear.homModule
variable {G : Type} [Group G] (H : Subgroup G)

def subgroupShapiroIso (A : Rep ℤ H) (n : ℕ) :
    groupHomology A n ≅ groupHomology (Rep.ind H.subtype A) n := by
  classical
  exact coefficientNaturalHomologyIso
      ((Rep.resFunctor H.subtype).mapProjectiveResolution (Rep.barResolution ℤ G)) A n ≪≫
    (homologyFunctor (ModuleCat ℤ) (ComplexShape.down ℕ) n).mapIso
      (groupHomology.coinvariantsTensorResProjectiveResolutionIso H A (Rep.barResolution ℤ G)) ≪≫
    ((homologyFunctor (ModuleCat ℤ) (ComplexShape.down ℕ) n).mapIso
      (groupHomology.inhomogeneousChainsIso (Rep.ind H.subtype A))).symm

theorem subgroupShapiro_return_chain [DecidableEq G] [DecidableEq H] (A : Rep ℤ G) :
    (groupHomology.inhomogeneousChainsIso (Rep.res H.subtype A)).hom ≫
      (((Rep.coinvariantsTensor ℤ H).obj (Rep.res H.subtype A)).mapHomologicalComplex _).map
        (subgroupBarResolutionMap H) ≫
      (groupHomology.coinvariantsTensorResProjectiveResolutionIso H
        (Rep.res H.subtype A) (Rep.barResolution ℤ G)).hom ≫
      coefficientTensorChainMap (Rep.barComplex ℤ G) (finiteIndexReturn H A) =
    subgroupBarInclusion H A ≫ (groupHomology.inhomogeneousChainsIso A).hom := by
  apply HomologicalComplex.Hom.ext
  funext i
  apply ModuleCat.hom_ext
  apply Finsupp.lhom_ext'
  intro x
  apply LinearMap.ext
  intro a
  change (coefficientTensorChainMap (Rep.barComplex ℤ G) (finiteIndexReturn H A)).f i
      ((groupHomology.coinvariantsTensorResProjectiveResolutionIso H
        (Rep.res H.subtype A) (Rep.barResolution ℤ G)).hom.f i
        ((((Rep.coinvariantsTensor ℤ H).obj (Rep.res H.subtype A)).map
          (subgroupFreeInclusion H i))
          (Rep.finsuppToCoinvariantsTensorFree (Rep.res H.subtype A) (Fin i → H)
            (Finsupp.single x a)))) =
    (groupHomology.inhomogeneousChainsIso A).hom.f i
      ((subgroupBarInclusion H A).f i (Finsupp.single x a))
  rw [Rep.finsuppToCoinvariantsTensorFree_single]
  change (coefficientTensorChainMap (Rep.barComplex ℤ G) (finiteIndexReturn H A)).f i
    (Rep.coinvariantsTensorIndInv H.subtype (Rep.res H.subtype A) (Rep.free ℤ G (Fin i → G))
      (Rep.coinvariantsTensorMk (Rep.res H.subtype A)
        (Rep.res H.subtype (Rep.free ℤ G (Fin i → G))) a
        ((subgroupFreeInclusion H i).hom (Finsupp.single x (MonoidAlgebra.single 1 1))))) = _
  rw [subgroupFreeInclusion_single, Subgroup.coe_one]
  have hi : Rep.coinvariantsTensorIndInv H.subtype (Rep.res H.subtype A)
      (Rep.free ℤ G (Fin i → G))
      (Rep.coinvariantsTensorMk (Rep.res H.subtype A)
        (Rep.res H.subtype (Rep.free ℤ G (Fin i → G))) a
        (Finsupp.single (H.subtype ∘ x) (MonoidAlgebra.single 1 1))) =
    Rep.coinvariantsTensorMk (Rep.ind H.subtype (Rep.res H.subtype A))
      (Rep.free ℤ G (Fin i → G))
      (Representation.IndV.mk H.subtype (Rep.res H.subtype A).ρ 1 a)
      (Finsupp.single (H.subtype ∘ x) (MonoidAlgebra.single 1 1)) :=
    Rep.coinvariantsTensorIndInv_mk_tmul_indMk H.subtype a _
  rw [hi]
  change Rep.coinvariantsTensorMk A (Rep.free ℤ G (Fin i → G))
      ((finiteIndexReturn H A).hom (Representation.IndV.mk H.subtype
        (Rep.res H.subtype A).ρ 1 a))
      (Finsupp.single (H.subtype ∘ x) (MonoidAlgebra.single 1 1)) = _
  rw [finiteIndexReturn_mk, inv_one, map_one]
  change Rep.coinvariantsTensorMk A (Rep.free ℤ G (Fin i → G)) a
      (Finsupp.single (H.subtype ∘ x) (MonoidAlgebra.single 1 1)) =
    Rep.finsuppToCoinvariantsTensorFree A (Fin i → G)
      ((subgroupBarInclusion H A).f i (Finsupp.single x a))
  rw [show (subgroupBarInclusion H A).f i (Finsupp.single x a) =
    Finsupp.single (H.subtype ∘ x) a from groupHomology.chainsMap_f_single _ _ _ _ _]
  rw [Rep.finsuppToCoinvariantsTensorFree_single]
  rfl

theorem subgroup_comparison_homology [DecidableEq G] [DecidableEq H]
    (A : Rep ℤ H) (n : ℕ) :
    (coefficientNaturalHomologyIso
      ((Rep.resFunctor H.subtype).mapProjectiveResolution (Rep.barResolution ℤ G)) A n).hom =
    homologyMap (groupHomology.inhomogeneousChainsIso A).hom n ≫
      homologyMap ((((Rep.coinvariantsTensor ℤ H).obj A).mapHomologicalComplex _).map
        (subgroupBarResolutionMap H)) n := by
  let Q : ProjectiveResolution (Rep.trivial ℤ H ℤ) :=
    (Rep.resFunctor H.subtype).mapProjectiveResolution (Rep.barResolution ℤ G)
  let u : Rep.barComplex ℤ H ⟶ Q.complex := subgroupBarResolutionMap H
  let v : Rep.barComplex ℤ H ⟶ Q.complex :=
    (ProjectiveResolution.homotopyEquiv (Rep.barResolution ℤ H) Q).hom
  have hv : Homotopy u v := subgroupBarResolutionHomotopy H
  have h := (((Rep.coinvariantsTensor ℤ H).obj A).mapHomotopy hv).homologyMap_eq n
  change homologyMap (groupHomology.inhomogeneousChainsIso A).hom n ≫
      homologyMap ((((Rep.coinvariantsTensor ℤ H).obj A).mapHomologicalComplex _).map
        v) n = homologyMap (groupHomology.inhomogeneousChainsIso A).hom n ≫
      homologyMap ((((Rep.coinvariantsTensor ℤ H).obj A).mapHomologicalComplex _).map u) n
  exact congrArg (fun f => homologyMap (groupHomology.inhomogeneousChainsIso A).hom n ≫ f) h.symm

end PolycyclicRecognition

end

end OAI
