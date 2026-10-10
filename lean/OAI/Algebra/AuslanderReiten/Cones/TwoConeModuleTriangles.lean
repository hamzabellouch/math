import OAI.Algebra.AuslanderReiten.Cones.TwoConeSkeleton
import OAI.Algebra.AuslanderReiten.Complete.ProjectiveCompleteResolution

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Pretriangulated
open scoped ModuleCat.Algebra

namespace ArExplicit.TwoCone

universe u
variable {k R : Type u} [Field k] [Ring R] [Algebra k R] [Module.Finite k R]
variable (D : Data R) (hf : ∀ n, Module.Finite k (D.term n))

abbrev termModule (n : ℕ) : FiniteLeftModule k R where
  carrier := D.term n
  scalar := inferInstance
  tower := inferInstance
  finite := hf n

abbrev baseCokernelModule (n : ℕ) : FiniteLeftModule k R where
  carrier := ModuleCat.of R (BaseCokernel D n)
  scalar := inferInstance
  tower := inferInstance
  finite := by let := hf n; infer_instance

abbrev middleCokernelModule (n : ℕ) : FiniteLeftModule k R where
  carrier := ModuleCat.of R (BaseCokernel D (n + 2) × BaseCokernel D (n + 2))
  scalar := inferInstance
  tower := inferInstance
  finite := by let := hf (n + 2); infer_instance

abbrev skeletonCokernelModule (n : ℕ) : FiniteLeftModule k R where
  carrier := ModuleCat.of R (SkeletonCokernel D n)
  scalar := inferInstance
  tower := inferInstance
  finite := by
    let := hf n
    let := hf (n + 2)
    infer_instance

abbrev cokernelModule (n : ℕ) : FiniteLeftModule k R where
  carrier := ModuleCat.of R (Cokernel D n)
  scalar := inferInstance
  tower := inferInstance
  finite := by
    let := hf n
    let := hf (n + 2)
    let := hf (n + 4)
    infer_instance

variable (τ : FrobeniusTrace k R)

theorem exists_skeleton_triangle
    (hex : ∀ n, Function.Exact (D.d (n + 1)) (D.d n)) (n : ℕ) :
    ∃ δ : (HomotopyCategory.quotient _ _).obj ((middleCokernelModule D hf n).completeCochain τ) ⟶
        ((HomotopyCategory.quotient _ _).obj ((baseCokernelModule D hf n).completeCochain τ))⟦(1 : ℤ)⟧,
      Triangle.mk
        ((HomotopyCategory.quotient _ _).map (FiniteLeftModule.resolutionMap τ
          (M := baseCokernelModule D hf n) (N := skeletonCokernelModule D hf n)
          (bottomCokernelInclusion D n)))
        ((HomotopyCategory.quotient _ _).map (FiniteLeftModule.resolutionMap τ
          (M := skeletonCokernelModule D hf n) (N := middleCokernelModule D hf n)
          (singletonCokernelProjection D n))) δ ∈
        distTriang (HomotopyCategory (ModuleCat.{u} R) (ComplexShape.up ℤ)) :=
  FiniteLeftModule.exists_resolution_triangle τ
    (M := baseCokernelModule D hf n) (N := skeletonCokernelModule D hf n)
    (L := middleCokernelModule D hf n)
    (bottomCokernelInclusion D n) (singletonCokernelProjection D n)
    (bottomCokernelInclusion_injective D hex n) (singletonCokernelProjection_surjective D n)
    (skeletonCokernel_exact D n)

theorem exists_top_triangle
    (hex : ∀ n, Function.Exact (D.d (n + 1)) (D.d n)) (n : ℕ) :
    ∃ δ : (HomotopyCategory.quotient _ _).obj ((baseCokernelModule D hf (n + 4)).completeCochain τ) ⟶
        ((HomotopyCategory.quotient _ _).obj ((skeletonCokernelModule D hf n).completeCochain τ))⟦(1 : ℤ)⟧,
      Triangle.mk
        ((HomotopyCategory.quotient _ _).map (FiniteLeftModule.resolutionMap τ
          (M := skeletonCokernelModule D hf n) (N := cokernelModule D hf n)
          (skeletonCokernelInclusion D n)))
        ((HomotopyCategory.quotient _ _).map (FiniteLeftModule.resolutionMap τ
          (M := cokernelModule D hf n) (N := baseCokernelModule D hf (n + 4))
          (topCokernelProjection D n))) δ ∈
        distTriang (HomotopyCategory (ModuleCat.{u} R) (ComplexShape.up ℤ)) :=
  FiniteLeftModule.exists_resolution_triangle τ
    (M := skeletonCokernelModule D hf n) (N := cokernelModule D hf n)
    (L := baseCokernelModule D hf (n + 4))
    (skeletonCokernelInclusion D n) (topCokernelProjection D n)
    (skeletonCokernelInclusion_injective D hex n) (topCokernelProjection_surjective D n)
    (topCokernel_exact D n)

variable (hex : ∀ n, Function.Exact (D.d (n + 1)) (D.d n))

def baseStepInclusion (n : ℕ) : BaseCokernel D (n + 1) →ₗ[R] D.term n :=
  (LinearMap.ker (LinearMap.range (D.d n)).mkQ).subtype.comp
    (baseSuccessorEquiv D hex n).toLinearMap

theorem baseStepInclusion_injective (n : ℕ) : Function.Injective (baseStepInclusion D hex n) :=
  Subtype.val_injective.comp (baseSuccessorEquiv D hex n).injective

theorem baseStep_exact (n : ℕ) :
    Function.Exact (baseStepInclusion D hex n) (LinearMap.range (D.d n)).mkQ := by
  intro x
  constructor
  · intro hx
    refine ⟨(baseSuccessorEquiv D hex n).symm ⟨x, hx⟩, ?_⟩
    exact congrArg Subtype.val ((baseSuccessorEquiv D hex n).apply_symm_apply ⟨x, hx⟩)
  · rintro ⟨y, rfl⟩
    exact ((baseSuccessorEquiv D hex n) y).property

def baseSuccessorShiftIso (hp : ∀ n, Module.Projective R (D.term n)) (n : ℕ) :
    (HomotopyCategory.quotient _ _).obj ((baseCokernelModule D hf n).completeCochain τ) ≅
      ((HomotopyCategory.quotient _ _).obj ((baseCokernelModule D hf (n + 1)).completeCochain τ))⟦(1 : ℤ)⟧ := by
  letI : Module.Projective R (D.term n) := hp n
  exact FiniteLeftModule.projectiveMiddleShiftIso τ
    (M := baseCokernelModule D hf (n + 1)) (N := termModule D hf n)
    (L := baseCokernelModule D hf n)
    (baseStepInclusion D hex n) (LinearMap.range (D.d n)).mkQ
    (baseStepInclusion_injective D hex n) ((LinearMap.range (D.d n)).mkQ_surjective) (baseStep_exact D hex n)

def baseIteratedShiftIso (hp : ∀ n, Module.Projective R (D.term n)) (n : ℕ) :
    (HomotopyCategory.quotient _ _).obj ((baseCokernelModule D hf 0).completeCochain τ) ≅
      ((HomotopyCategory.quotient _ _).obj ((baseCokernelModule D hf n).completeCochain τ))⟦(n : ℤ)⟧ := by
  induction n with
  | zero =>
    exact ((shiftFunctorZero (HomotopyCategory (ModuleCat.{u} R) (ComplexShape.up ℤ)) ℤ).app _).symm
  | succ n ih =>
    exact ih ≪≫
      (CategoryTheory.shiftFunctor (HomotopyCategory (ModuleCat.{u} R) (ComplexShape.up ℤ)) (n : ℤ)).mapIso
        (baseSuccessorShiftIso D hf τ hex hp n) ≪≫
      (shiftFunctorAdd' (HomotopyCategory (ModuleCat.{u} R) (ComplexShape.up ℤ))
        1 (n : ℤ) ((n + 1 : ℕ) : ℤ) (by omega)).symm.app _

end ArExplicit.TwoCone

end

end OAI
