import OAI.GroupTheory.PolycyclicRecognition.Analysis.IntegralFinsuppFunctor
import OAI.GroupTheory.PolycyclicRecognition.Finiteness.NormalExtensionBicomplex

namespace OAI

/-! # Coinvariant tensor with a free coefficient representation

This functor is a finite-support sum of the underlying module functor, so it
preserves homology. The comparison keeps the actual group-ring action.
-/

noncomputable section
namespace PolycyclicRecognition
open CategoryTheory MonoidalCategory
open scoped TensorProduct
attribute [local instance 2000] Rep.hV2 Rep.instLinear
attribute [local instance 2200] TensorProduct.instModule
attribute [local instance 2300] Representation.Coinvariants.instModule
attribute [local instance 2300] Finsupp.module
variable {G : Type} [Group G] (ι : Type)

theorem tensorFreeToFinsupp_natural [DecidableEq ι] (A B : Rep.{0} ℤ G) (f : A ⟶ B)
    (a : A.V) (u : (Rep.free ℤ G ι).V) :
    Rep.coinvariantsTensorFreeToFinsupp B ι
        (Representation.Coinvariants.mk _ (f.hom a ⊗ₜ[ℤ] u)) =
      (Finsupp.mapRange.linearMap f.hom.toLinearMap)
        (Rep.coinvariantsTensorFreeToFinsupp A ι
          (Representation.Coinvariants.mk _ (a ⊗ₜ[ℤ] u))) := by
  classical
  induction u using Finsupp.induction_linear with
  | zero =>
    simp only [TensorProduct.tmul_zero, map_zero]
  | add u v hu hv => simp only [TensorProduct.tmul_add, map_add, hu, hv]
  | single i c =>
    induction c using MonoidAlgebra.induction_linear with
    | zero =>
      simp only [Finsupp.single_zero, TensorProduct.tmul_zero, map_zero]
    | add c d hc hd =>
      simp only [Finsupp.single_add, TensorProduct.tmul_add, map_add, hc, hd]
    | single g r =>
      have hB := Rep.coinvariantsTensorFreeToFinsupp_mk_tmul_single B (f.hom a) i g r
      have hA := Rep.coinvariantsTensorFreeToFinsupp_mk_tmul_single A a i g r
      refine hB.trans (Eq.trans ?_
        (congrArg (Finsupp.mapRange.linearMap f.hom.toLinearMap) hA.symm))
      simp only [Finsupp.mapRange.linearMap_apply, Finsupp.mapRange_single]
      apply congrArg (Finsupp.single i)
      exact ((f.hom.toLinearMap.map_smul r _).trans
        (congrArg (fun x => @SMul.smul ℤ B.V B.hV2.toSMul r x)
          (Rep.hom_comm_apply f g⁻¹ a))).symm

def freeCoefficientCoinvariantsIso :
    (Rep.coinvariantsTensor ℤ G).obj (Rep.free ℤ G ι) ≅
      forget₂ (Rep.{0} ℤ G) (ModuleCat ℤ) ⋙ moduleFinsuppFunctor ℤ ι := by
  classical
  refine NatIso.ofComponents (fun A =>
    (Rep.coinvariantsFunctor ℤ G).mapIso (β_ (Rep.free ℤ G ι) A) ≪≫
      (Rep.coinvariantsTensorFreeLEquiv A ι).toModuleIso) ?_
  intro A B f
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  induction x using Representation.Coinvariants.induction_on with
  | h x =>
    induction x using TensorProduct.inductionOn with
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul u a =>
      exact tensorFreeToFinsupp_natural ι A B f a u

end PolycyclicRecognition

end

end OAI
