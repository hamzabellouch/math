import OAI.GroupTheory.PolycyclicRecognition.Algebra.NormalInductionExact
import Mathlib.RepresentationTheory.Homological.GroupHomology.Shapiro

namespace OAI

/-! # Tensoring an induced resolution

The projection formula, with the tensor factors in resolution order, identifies
an induced resolution with subgroup homology for restricted coefficients.
-/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped TensorProduct
attribute [local instance 2000] Rep.hV2 Rep.instLinear
attribute [local instance 2100] Linear.homModule
attribute [local instance 2200] TensorProduct.instModule
attribute [local instance 2300] Representation.Coinvariants.instModule
variable {G : Type} [Group G] (N : Subgroup G) (A : Rep ℤ G)

theorem coinvariantsBraiding_mk (B C : Rep ℤ G) (b : B) (c : C) :
    ((Rep.coinvariantsFunctor ℤ G).map (β_ B C).hom)
      (Rep.coinvariantsTensorMk B C b c) = Rep.coinvariantsTensorMk C B c b := rfl

theorem coinvariantsTensorMap_mk {B C : Rep ℤ G} (f : B ⟶ C)
    (a : A) (b : B) :
    (((Rep.coinvariantsTensor ℤ G).obj A).map f)
      (Rep.coinvariantsTensorMk A B a b) = Rep.coinvariantsTensorMk A C a (f.hom b) := rfl

def inducedTensorRightIso (B : Rep ℤ N) :
    ((Rep.coinvariantsTensor ℤ G).obj A).obj (Rep.ind N.subtype B) ≅
      ((Rep.coinvariantsTensor ℤ N).obj (Rep.res N.subtype A)).obj B :=
  (Rep.coinvariantsFunctor ℤ G).mapIso (β_ A (Rep.ind N.subtype B)) ≪≫
    Rep.coinvariantsTensorIndIso N.subtype B A ≪≫
      (Rep.coinvariantsFunctor ℤ N).mapIso (β_ B (Rep.res N.subtype A))

@[simp] theorem inducedTensorRightIso_mk (B : Rep ℤ N) (a : A) (g : G) (b : B) :
    (inducedTensorRightIso N A B).hom
      (Rep.coinvariantsTensorMk A (Rep.ind N.subtype B) a
        (Representation.IndV.mk N.subtype B.ρ g b)) =
      Rep.coinvariantsTensorMk (Rep.res N.subtype A) B (A.ρ g a) b := by
  change ((Rep.coinvariantsFunctor ℤ N).map (β_ B (Rep.res N.subtype A)).hom)
    (Rep.coinvariantsTensorIndHom N.subtype B A
      (((Rep.coinvariantsFunctor ℤ G).map (β_ A (Rep.ind N.subtype B)).hom)
        (Rep.coinvariantsTensorMk A (Rep.ind N.subtype B) a
          (Representation.IndV.mk N.subtype B.ρ g b)))) = _
  rw [coinvariantsBraiding_mk, Rep.coinvariantsTensorIndHom_mk_tmul_indVMk,
    coinvariantsBraiding_mk]

def inducedTensorRightNatIso :
    Rep.indFunctor ℤ N.subtype ⋙ (Rep.coinvariantsTensor ℤ G).obj A ≅
      (Rep.coinvariantsTensor ℤ N).obj (Rep.res N.subtype A) :=
  NatIso.ofComponents (inducedTensorRightIso N A) (by
    intro B C f
    apply Rep.coinvariantsTensor_hom_ext
    apply DFunLike.ext
    intro a
    apply Representation.IndV.hom_ext
    intro g
    apply DFunLike.ext
    intro b
    change (inducedTensorRightIso N A C).hom
      ((((Rep.coinvariantsTensor ℤ G).obj A).map (Rep.indMap N.subtype f))
        (Rep.coinvariantsTensorMk A (Rep.ind N.subtype B) a
          (Representation.IndV.mk N.subtype B.ρ g b))) =
      (((Rep.coinvariantsTensor ℤ N).obj (Rep.res N.subtype A)).map f)
        ((inducedTensorRightIso N A B).hom
          (Rep.coinvariantsTensorMk A (Rep.ind N.subtype B) a
            (Representation.IndV.mk N.subtype B.ρ g b)))
    rw [coinvariantsTensorMap_mk, normalInductionMap_mk, inducedTensorRightIso_mk,
      inducedTensorRightIso_mk, coinvariantsTensorMap_mk])

section Normal
variable [N.Normal]

def inducedResolutionTensorIso
    (P : ProjectiveResolution (Rep.trivial ℤ N ℤ)) :
    (normalInducedResolution ℤ N P).complex.coinvariantsTensorObj A ≅
      P.complex.coinvariantsTensorObj (Rep.res N.subtype A) :=
  (NatIso.mapHomologicalComplex (inducedTensorRightNatIso N A) (ComplexShape.down ℕ)).app
    P.complex

def inducedResolutionHomologyIso
    (P : ProjectiveResolution (Rep.trivial ℤ N ℤ)) (i : ℕ) :
    ((normalInducedResolution ℤ N P).complex.coinvariantsTensorObj A).homology i ≅
      groupHomology (Rep.res N.subtype A) i := by
  classical
  exact (HomologicalComplex.homologyFunctor (ModuleCat ℤ) (ComplexShape.down ℕ) i).mapIso
    (inducedResolutionTensorIso N A P) ≪≫
      (groupHomologyIso (Rep.res N.subtype A) i P).symm

end Normal

end PolycyclicRecognition

end

end OAI
