import OAI.Algebra.AuslanderReiten.Cones.TwoConeModuleTriangles
import OAI.Algebra.AuslanderReiten.Stable.CanonicalCosyzygyShift

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
variable (hp : ∀ n, Module.Projective R (D.term n))

def coneTailData : Data R where
  term := term D
  d := d D
  first _ := 0
  second _ := 0
  square := d_square D
  first_comm _ := by simp
  second_comm _ := by simp
  comparisons_comm _ := by simp

abbrev coneTermModule (n : ℕ) : FiniteLeftModule k R where
  carrier := term D n
  scalar := inferInstance
  tower := inferInstance
  finite := by
    let := hf n
    let := hf (n + 2)
    let := hf (n + 4)
    infer_instance

def cokernelSuccessorShiftIso (n : ℕ) :
    (HomotopyCategory.quotient _ _).obj ((cokernelModule D hf n).completeCochain τ) ≅
      ((HomotopyCategory.quotient _ _).obj ((cokernelModule D hf (n + 1)).completeCochain τ))⟦(1 : ℤ)⟧ := by
  letI : Module.Projective R (term D n) := term_projective D hp n
  exact FiniteLeftModule.projectiveMiddleShiftIso τ
    (M := cokernelModule D hf (n + 1)) (N := coneTermModule D hf n)
    (L := cokernelModule D hf n)
    (baseStepInclusion (coneTailData D) (d_exact D hex) n) (LinearMap.range (d D n)).mkQ
    (baseStepInclusion_injective (coneTailData D) (d_exact D hex) n)
    ((LinearMap.range (d D n)).mkQ_surjective) (baseStep_exact (coneTailData D) (d_exact D hex) n)

def stableRepresentativeIso :
    (HomotopyCategory.quotient _ _).obj ((cokernelModule D hf 0).completeCochain τ) ≅
      (HomotopyCategory.quotient _ _).obj
        (((cokernelModule D hf 1).canonicalCosyzygies 1).completeCochain τ) :=
  cokernelSuccessorShiftIso D hf τ hex hp 0 ≪≫
    (FiniteLeftModule.canonicalCosyzygiesShiftIso τ (cokernelModule D hf 1) 1).symm

def branchTargetShiftIso :
    (HomotopyCategory.quotient _ _).obj
        (((cokernelModule D hf 1).canonicalCosyzygies 4).completeCochain τ) ≅
      ((HomotopyCategory.quotient _ _).obj ((cokernelModule D hf 0).completeCochain τ))⟦(3 : ℤ)⟧ :=
  FiniteLeftModule.canonicalCosyzygiesShiftIso τ (cokernelModule D hf 1) 4 ≪≫
    ((CategoryTheory.shiftFunctor (HomotopyCategory (ModuleCat.{u} R) (ComplexShape.up ℤ)) 3).mapIso
      (cokernelSuccessorShiftIso D hf τ hex hp 0) ≪≫
      (shiftFunctorAdd' (HomotopyCategory (ModuleCat.{u} R) (ComplexShape.up ℤ))
        1 3 4 (by decide)).symm.app _).symm

end ArExplicit.TwoCone

end

end OAI
