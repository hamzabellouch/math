import OAI.Algebra.AuslanderReiten.Cones.TwoConeExtensionDiagrams
import OAI.Algebra.AuslanderReiten.Modules.FiniteModuleNaturality

namespace OAI

noncomputable section
open CategoryTheory
open scoped ModuleCat.Algebra

namespace ArExplicit.TwoCone

universe u
variable {k R : Type u} [Field k] [Ring R] [Algebra k R] [Module.Finite k R]
variable (D : Data R) (hf : ∀ n, Module.Finite k (D.term n))
variable (τ : FrobeniusTrace k R)
variable (hex : ∀ n, Function.Exact (D.d (n + 1)) (D.d n))

abbrev middleTermModule (n : ℕ) : FiniteLeftModule k R where
  carrier := ModuleCat.of R (middleTerm D n)
  scalar := inferInstance
  tower := inferInstance
  finite := by let := hf (n + 2); infer_instance

def middleCoverQuotient (n : ℕ) : middleTerm D n →ₗ[R]
    (BaseCokernel D (n + 2) × BaseCokernel D (n + 2)) :=
  ((LinearMap.range (D.d (n + 2))).mkQ).prodMap ((LinearMap.range (D.d (n + 2))).mkQ)

theorem middleCoverQuotient_surjective (n : ℕ) : Function.Surjective (middleCoverQuotient D n) := by
  rintro ⟨x, y⟩
  obtain ⟨x, rfl⟩ := (LinearMap.range (D.d (n + 2))).mkQ_surjective x
  obtain ⟨y, rfl⟩ := (LinearMap.range (D.d (n + 2))).mkQ_surjective y
  exact ⟨(x, y), rfl⟩

theorem middleStepInclusion_injective (n : ℕ) : Function.Injective (middleStepInclusion D hex n) := by
  rintro ⟨x, y⟩ ⟨x', y'⟩ h
  exact Prod.ext ((baseStepInclusion_injective D hex (n + 2)) (congrArg Prod.fst h))
    ((baseStepInclusion_injective D hex (n + 2)) (congrArg Prod.snd h))

theorem middleStep_exact (n : ℕ) :
    Function.Exact (middleStepInclusion D hex n) (middleCoverQuotient D n) := by
  rintro ⟨x, y⟩
  constructor
  · intro h
    obtain ⟨a, ha⟩ := (baseStep_exact D hex (n + 2) x).mp (congrArg Prod.fst h)
    obtain ⟨b, hb⟩ := (baseStep_exact D hex (n + 2) y).mp (congrArg Prod.snd h)
    exact ⟨(a, b), Prod.ext ha hb⟩
  · rintro ⟨⟨a, b⟩, h⟩
    exact Prod.ext ((baseStep_exact D hex (n + 2) x).mpr ⟨a, congrArg Prod.fst h⟩)
      ((baseStep_exact D hex (n + 2) y).mpr ⟨b, congrArg Prod.snd h⟩)

def middleSuccessorShiftIso (hp : ∀ n, Module.Projective R (D.term n)) (n : ℕ) :
    (HomotopyCategory.quotient _ _).obj ((middleCokernelModule D hf n).completeCochain τ) ≅
      ((HomotopyCategory.quotient _ _).obj ((middleCokernelModule D hf (n + 1)).completeCochain τ))⟦(1 : ℤ)⟧ := by
  letI := hp (n + 2)
  exact FiniteLeftModule.projectiveMiddleShiftIso τ
    (M := middleCokernelModule D hf (n + 1)) (N := middleTermModule D hf n)
    (L := middleCokernelModule D hf n)
    (middleStepInclusion D hex n) (middleCoverQuotient D n)
    (middleStepInclusion_injective D hex n) (middleCoverQuotient_surjective D n)
    (middleStep_exact D hex n)

abbrev skeletonConnecting (n : ℕ) :=
  FiniteLeftModule.resolutionConnecting τ
    (M := baseCokernelModule D hf n) (N := skeletonCokernelModule D hf n)
    (L := middleCokernelModule D hf n)
    (bottomCokernelInclusion D n) (singletonCokernelProjection D n)
    (bottomCokernelInclusion_injective D hex n) (singletonCokernelProjection_surjective D n)
    (skeletonCokernel_exact D n)

abbrev topConnecting (n : ℕ) :=
  FiniteLeftModule.resolutionConnecting τ
    (M := skeletonCokernelModule D hf n) (N := cokernelModule D hf n)
    (L := baseCokernelModule D hf (n + 4))
    (skeletonCokernelInclusion D n) (topCokernelProjection D n)
    (skeletonCokernelInclusion_injective D hex n) (topCokernelProjection_surjective D n)
    (topCokernel_exact D n)

theorem skeletonConnecting_eq (hp : ∀ n, Module.Projective R (D.term n)) (n : ℕ) :
    skeletonConnecting D hf τ hex n = (middleSuccessorShiftIso D hf τ hex hp n).hom ≫
      (CategoryTheory.shiftFunctor (HomotopyCategory (ModuleCat.{u} R) (ComplexShape.up ℤ)) 1).map
        ((HomotopyCategory.quotient _ _).map (FiniteLeftModule.resolutionMap τ
          (M := middleCokernelModule D hf (n + 1)) (N := baseCokernelModule D hf n)
          (rowCokernelMap D n))) := by
  have h := FiniteLeftModule.resolutionConnecting_natural τ
    (M₁ := middleCokernelModule D hf (n + 1)) (N₁ := middleTermModule D hf n)
    (L₁ := middleCokernelModule D hf n)
    (M₂ := baseCokernelModule D hf n) (N₂ := skeletonCokernelModule D hf n)
    (L₂ := middleCokernelModule D hf n)
    (middleStepInclusion D hex n) (middleCoverQuotient D n)
    (bottomCokernelInclusion D n) (singletonCokernelProjection D n)
    (middleStepInclusion_injective D hex n) (middleCoverQuotient_surjective D n) (middleStep_exact D hex n)
    (bottomCokernelInclusion_injective D hex n) (singletonCokernelProjection_surjective D n)
    (skeletonCokernel_exact D n)
    (rowCokernelMap D n) (singletonCoverLift D n) LinearMap.id
    (singletonCoverLift_boundary D hex n)
    (by simpa only [LinearMap.id_comp, middleCoverQuotient] using singletonCoverLift_projection D n)
  rw [FiniteLeftModule.resolutionMap_id τ (M := middleCokernelModule D hf n), Category.id_comp] at h
  let := hp (n + 2)
  simpa only [skeletonConnecting, middleSuccessorShiftIso,
    FiniteLeftModule.projectiveMiddleShiftIso_hom] using h

theorem topConnecting_eq (hp : ∀ n, Module.Projective R (D.term n)) (n : ℕ) :
    topConnecting D hf τ hex n = (baseSuccessorShiftIso D hf τ hex hp (n + 4)).hom ≫
      (CategoryTheory.shiftFunctor (HomotopyCategory (ModuleCat.{u} R) (ComplexShape.up ℤ)) 1).map
        ((HomotopyCategory.quotient _ _).map (FiniteLeftModule.resolutionMap τ
          (M := baseCokernelModule D hf (n + 5)) (N := skeletonCokernelModule D hf n)
          (-(topAttachingCokernel D n)))) := by
  have h := FiniteLeftModule.resolutionConnecting_natural τ
    (M₁ := baseCokernelModule D hf (n + 5)) (N₁ := termModule D hf (n + 4))
    (L₁ := baseCokernelModule D hf (n + 4))
    (M₂ := skeletonCokernelModule D hf n) (N₂ := cokernelModule D hf n)
    (L₂ := baseCokernelModule D hf (n + 4))
    (baseStepInclusion D hex (n + 4)) (LinearMap.range (D.d (n + 4))).mkQ
    (skeletonCokernelInclusion D n) (topCokernelProjection D n)
    (baseStepInclusion_injective D hex (n + 4)) (Submodule.mkQ_surjective _) (baseStep_exact D hex (n + 4))
    (skeletonCokernelInclusion_injective D hex n) (topCokernelProjection_surjective D n)
    (topCokernel_exact D n)
    (-(topAttachingCokernel D n)) (topCoverLift D n) LinearMap.id
    (topCoverLift_boundary D hex n)
    (by simpa only [LinearMap.id_comp] using topCoverLift_projection D n)
  rw [FiniteLeftModule.resolutionMap_id τ (M := baseCokernelModule D hf (n + 4)), Category.id_comp] at h
  let := hp (n + 4)
  simpa only [topConnecting, baseSuccessorShiftIso,
    FiniteLeftModule.projectiveMiddleShiftIso_hom] using h

end ArExplicit.TwoCone

end

end OAI
