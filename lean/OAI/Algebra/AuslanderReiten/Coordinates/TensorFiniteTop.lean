import OAI.Algebra.AuslanderReiten.Coordinates.TensorTopCoverSquares
import OAI.Algebra.AuslanderReiten.Coordinates.TensorFiniteLift
import OAI.Algebra.AuslanderReiten.Cones.TwoConeIteration

namespace OAI

noncomputable section
namespace ArExplicit.T
open CategoryTheory
open scoped TensorProduct
universe u
variable {k : Type u} [Field k] [CharP k 2] (q : k) (H : kˣ)
attribute [local instance 2000] moduleCatBaseModule moduleCatBaseTower
local notation "R" => T k q
local notation "Ae" => ExternalTensor.EnvelopingProduct k R R
local notation "D" => bimoduleTwoConeData q
local notation "Q" => sourceData q H
local notation "τ" => AEnvelopingFrobeniusTrace k q
local notation "hD" => bimodule_term_finite_k q
local notation "hQ" => source_term_finite_k q H

private theorem topOneShift_natural (n : ℕ) :
    (HomotopyCategory.quotient _ _).map (FiniteLeftModule.resolutionMap τ
      (M := TwoCone.baseCokernelModule Q hQ n) (N := TwoCone.baseCokernelModule D hD (n+1))
      (bimoduleTopCokernel q H n)) ≫
        (TwoCone.baseSuccessorShiftIso D hD τ (bimodule_exact q) (bimodule_term_projective q) (n+1)).hom =
    (TwoCone.baseSuccessorShiftIso Q hQ τ (source_exact q H) (source_projective q H) n).hom ≫
      (CategoryTheory.shiftFunctor (HomotopyCategory (ModuleCat.{u} Ae) (ComplexShape.up ℤ)) (1 : ℤ)).map
        ((HomotopyCategory.quotient _ _).map (FiniteLeftModule.resolutionMap τ
          (M := TwoCone.baseCokernelModule Q hQ (n+1)) (N := TwoCone.baseCokernelModule D hD (n+2))
          (bimoduleTopCokernel q H (n+1)))) := by
  have h := FiniteLeftModule.resolutionConnecting_natural τ
    (M₁ := TwoCone.baseCokernelModule Q hQ (n+1)) (N₁ := TwoCone.termModule Q hQ n)
    (L₁ := TwoCone.baseCokernelModule Q hQ n)
    (M₂ := TwoCone.baseCokernelModule D hD (n+2)) (N₂ := TwoCone.termModule D hD (n+1))
    (L₂ := TwoCone.baseCokernelModule D hD (n+1))
    (TwoCone.baseStepInclusion Q (source_exact q H) n) (LinearMap.range ((Q).d n)).mkQ
    (TwoCone.baseStepInclusion D (bimodule_exact q) (n+1)) (LinearMap.range ((D).d (n+1))).mkQ
    (TwoCone.baseStepInclusion_injective Q (source_exact q H) n) (Submodule.mkQ_surjective _)
    (TwoCone.baseStep_exact Q (source_exact q H) n)
    (TwoCone.baseStepInclusion_injective D (bimodule_exact q) (n+1)) (Submodule.mkQ_surjective _)
    (TwoCone.baseStep_exact D (bimodule_exact q) (n+1))
    (bimoduleTopCokernel q H (n+1)) (bimoduleTopComparison q H n) (bimoduleTopCokernel q H n)
    (topCover_left q H n) (topCover_right q H n)
  let := bimodule_term_projective q (n+1)
  let := source_projective q H n
  simpa only [TwoCone.baseSuccessorShiftIso, FiniteLeftModule.projectiveMiddleShiftIso_hom] using h

def topFourShiftIso := iteratedShiftIso (fun n => TwoCone.baseResolution D hD τ (n+1))
  (fun n => TwoCone.baseSuccessorShiftIso D hD τ (bimodule_exact q)
    (bimodule_term_projective q) (n+1)) 4

theorem topFourShift_natural :
    (HomotopyCategory.quotient _ _).map (FiniteLeftModule.resolutionMap τ
      (M := TwoCone.baseCokernelModule Q hQ 0) (N := TwoCone.baseCokernelModule D hD 1)
      (bimoduleTopCokernel q H 0)) ≫ (topFourShiftIso q).hom =
    (TwoCone.baseIteratedShiftIso Q hQ τ (source_exact q H) (source_projective q H) 4).hom ≫
      (CategoryTheory.shiftFunctor (HomotopyCategory (ModuleCat.{u} Ae) (ComplexShape.up ℤ)) (4 : ℤ)).map
        ((HomotopyCategory.quotient _ _).map (FiniteLeftModule.resolutionMap τ
          (M := TwoCone.baseCokernelModule Q hQ 4) (N := TwoCone.baseCokernelModule D hD 5)
          (bimoduleTopCokernel q H 4))) := by
  have h := iteratedShiftIso_natural
    (Y := TwoCone.baseResolution Q hQ τ)
    (s := TwoCone.baseSuccessorShiftIso Q hQ τ (source_exact q H) (source_projective q H))
    (Z := fun n => TwoCone.baseResolution D hD τ (n+1))
    (fun n => TwoCone.baseSuccessorShiftIso D hD τ (bimodule_exact q) (bimodule_term_projective q) (n+1))
    (fun n => (HomotopyCategory.quotient _ _).map (FiniteLeftModule.resolutionMap τ
      (M := TwoCone.baseCokernelModule Q hQ n) (N := TwoCone.baseCokernelModule D hD (n+1))
      (bimoduleTopCokernel q H n))) (topOneShift_natural q H) 4
  simp only [topFourShiftIso, TwoCone.baseIteratedShiftIso_eq_iterated, Nat.cast_ofNat] at h ⊢
  convert! h using 1

theorem sourceFourthToTail_top :
    (TwoCone.topCokernelMap D 1).comp (sourceFourthToTail q H) = bimoduleTopCokernel q H 4 := by
  apply LinearMap.ext
  intro x
  change TwoCone.topCokernelMap D 1 (tailMap q H ((sourceFourthEquiv q H).symm x)) = _
  calc
    _ = topSyzygyMap q H ((sourceFourthEquiv q H).symm x) :=
      LinearMap.congr_fun (tailMap_top q H) _
    _ = bimoduleTopCokernel q H 4
        ((sourceFourthEquiv q H) ((sourceFourthEquiv q H).symm x)) :=
      (LinearMap.congr_fun (bimoduleTopCokernel_four q H) _).symm
    _ = bimoduleTopCokernel q H 4 x := by rw [LinearEquiv.apply_symm_apply]

theorem resolutionTailTop :
    (HomotopyCategory.quotient _ _).map (FiniteLeftModule.resolutionMap τ
      (M := TwoCone.baseCokernelModule Q hQ 4) (N := firstTailModule q) (sourceFourthToTail q H)) ≫
    (HomotopyCategory.quotient _ _).map (FiniteLeftModule.resolutionMap τ
      (M := firstTailModule q) (N := TwoCone.baseCokernelModule D hD 5) (TwoCone.topCokernelMap D 1)) =
    (HomotopyCategory.quotient _ _).map (FiniteLeftModule.resolutionMap τ
      (M := TwoCone.baseCokernelModule Q hQ 4) (N := TwoCone.baseCokernelModule D hD 5)
      (bimoduleTopCokernel q H 4)) := by
  calc
    _ = (HomotopyCategory.quotient _ _).map (FiniteLeftModule.resolutionMap τ
        (M := TwoCone.baseCokernelModule Q hQ 4) (N := TwoCone.baseCokernelModule D hD 5)
        ((TwoCone.topCokernelMap D 1).comp (sourceFourthToTail q H))) :=
      (FiniteLeftModule.resolutionMap_comp τ
        (M := TwoCone.baseCokernelModule Q hQ 4) (N := firstTailModule q)
        (L := TwoCone.baseCokernelModule D hD 5)
        (sourceFourthToTail q H) (TwoCone.topCokernelMap D 1)).symm
    _ = _ := congrArg (fun f => (HomotopyCategory.quotient _ _).map
      (FiniteLeftModule.resolutionMap τ
        (M := TwoCone.baseCokernelModule Q hQ 4) (N := TwoCone.baseCokernelModule D hD 5) f))
      (sourceFourthToTail_top q H)

def finiteTargetTop :
    (HomotopyCategory.quotient _ _).obj
      (((firstTailModule q).canonicalCosyzygies 4).completeCochain τ) ⟶
    TwoCone.baseResolution D hD τ 1 :=
  (FiniteLeftModule.canonicalCosyzygiesShiftIso τ (firstTailModule q) 4).hom ≫
    (CategoryTheory.shiftFunctor (HomotopyCategory (ModuleCat.{u} Ae) (ComplexShape.up ℤ)) (4 : ℤ)).map
      ((HomotopyCategory.quotient _ _).map (FiniteLeftModule.resolutionMap τ
        (M := firstTailModule q) (N := TwoCone.baseCokernelModule D hD 5)
        (TwoCone.topCokernelMap D 1))) ≫ (topFourShiftIso q).inv

def finiteSourceTop : (twistedFiniteModule (sourceTwist q H)).carrier →ₗ[Ae]
    (TwoCone.baseCokernelModule D hD 1).carrier :=
  (bimoduleTopCokernel q H 0).comp (sourceAugmentationEquiv q H).toLinearMap

theorem finiteLift_top :
    (HomotopyCategory.quotient _ _).map
      (FiniteLeftModule.resolutionMap τ (finiteLift q H)) ≫ finiteTargetTop q =
    (HomotopyCategory.quotient _ _).map
      (FiniteLeftModule.resolutionMap τ (finiteSourceTop q H)) := by
  rw [finiteLift_spec]
  dsimp only [finiteLiftClass, FiniteLeftModule.shiftedResolutionMap, finiteTargetTop]
  simp only [Category.assoc, Iso.inv_hom_id_assoc, Nat.cast_ofNat]
  erw [← Functor.map_comp_assoc]
  rw [resolutionTailTop q H]
  simp only [sourceShiftIso, TwoCone.tailSourceShiftIso, Iso.trans_hom, Category.assoc]
  have h := congrArg (fun f => f ≫ (topFourShiftIso q).inv) (topFourShift_natural q H)
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id] at h
  rw [← h, FiniteLeftModule.resolutionIso_hom]
  exact (FiniteLeftModule.resolutionMap_comp τ
    (M := twistedFiniteModule (sourceTwist q H)) (N := TwoCone.baseCokernelModule Q hQ 0)
    (L := TwoCone.baseCokernelModule D hD 1)
    (sourceAugmentationEquiv q H).toLinearMap (bimoduleTopCokernel q H 0)).symm

end ArExplicit.T

end

end OAI
