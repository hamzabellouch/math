import OAI.Algebra.AuslanderReiten.Resolutions.CubicCoverSquares
import OAI.Algebra.AuslanderReiten.Cones.TwoConeEvaluatedBoundary
import OAI.Algebra.AuslanderReiten.Coordinates.IteratedShiftNaturality

namespace OAI

noncomputable section
namespace ArExplicit.TwoCone
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra
universe u
variable {k R : Type u} [Field k] [Ring R] [Algebra k R] [Module.Finite k R]
variable (D : Data (R ⊗[k] Rᵐᵒᵖ)) (hf : ∀ n, Module.Finite k (D.term n))
variable (hex : ∀ n, Function.Exact (D.d (n+1)) (D.d n))
variable (hr : ∀ n, Module.Projective Rᵐᵒᵖ
  (EnvelopingBimodule k R (baseCokernelModule D hf n).carrier))
variable (hp : ∀ n, Module.Projective (R ⊗[k] Rᵐᵒᵖ) (D.term n))
variable (X : FiniteLeftModule k R) (τ : FrobeniusTrace k R)
local notation "HC" => HomotopyCategory (ModuleCat R) (ComplexShape.up ℤ)
local notation "Q" => HomotopyCategory.quotient (ModuleCat R) (ComplexShape.up ℤ)

abbrev evaluatedBase (n : ℕ) := (Q).obj
  ((X.evaluated (baseCokernelModule D hf n)).completeCochain τ)

def evaluatedFirstCokernel (n : ℕ) :
    evaluatedBase D hf X τ (n+3) ⟶ evaluatedBase D hf X τ n :=
  (Q).map (FiniteLeftModule.resolutionMap τ
    (FiniteLeftModule.evaluationMap X
      (M := baseCokernelModule D hf (n+3)) (N := baseCokernelModule D hf n)
      (firstCokernelMap D n)))

def evaluatedSecondCokernel (n : ℕ) :
    evaluatedBase D hf X τ (n+3) ⟶ evaluatedBase D hf X τ n :=
  (Q).map (FiniteLeftModule.resolutionMap τ
    (FiniteLeftModule.evaluationMap X
      (M := baseCokernelModule D hf (n+3)) (N := baseCokernelModule D hf n)
      (secondCokernelMap D n)))

theorem evaluatedFirstCokernel_step (n : ℕ) :
    evaluatedFirstCokernel D hf X τ n ≫
      (evaluatedBaseSuccessorIso D hf hex hr hp X τ n).hom =
    (evaluatedBaseSuccessorIso D hf hex hr hp X τ (n+3)).hom ≫
      (CategoryTheory.shiftFunctor HC (1 : ℤ)).map
        (evaluatedFirstCokernel D hf X τ (n+1)) := by
  let := hr n
  let := hr (n+3)
  let := hp n
  let := hp (n+3)
  have h := FiniteLeftModule.evaluationConnecting_natural X τ
    (M₁ := baseCokernelModule D hf (n+4)) (N₁ := termModule D hf (n+3))
    (P₁ := baseCokernelModule D hf (n+3))
    (M₂ := baseCokernelModule D hf (n+1)) (N₂ := termModule D hf n)
    (P₂ := baseCokernelModule D hf n)
    (baseStepInclusion D hex (n+3)) (LinearMap.range (D.d (n+3))).mkQ
    (baseStepInclusion D hex n) (LinearMap.range (D.d n)).mkQ
    (baseStepInclusion_injective D hex (n+3)) (Submodule.mkQ_surjective _) (baseStep_exact D hex (n+3))
    (baseStepInclusion_injective D hex n) (Submodule.mkQ_surjective _) (baseStep_exact D hex n)
    (firstCokernelMap D (n+1)) (D.first n) (firstCokernelMap D n)
    (firstCokernelMap_cover D hex n) (firstCokernelMap_quotient D n)
  simp only [evaluatedFirstCokernel, evaluatedBaseSuccessorIso,
    FiniteLeftModule.evaluationSuccessorIso_hom]
  convert! h using 1

theorem evaluatedSecondCokernel_step (n : ℕ) :
    evaluatedSecondCokernel D hf X τ n ≫
      (evaluatedBaseSuccessorIso D hf hex hr hp X τ n).hom =
    (evaluatedBaseSuccessorIso D hf hex hr hp X τ (n+3)).hom ≫
      (CategoryTheory.shiftFunctor HC (1 : ℤ)).map
        (evaluatedSecondCokernel D hf X τ (n+1)) := by
  let := hr n
  let := hr (n+3)
  let := hp n
  let := hp (n+3)
  have h := FiniteLeftModule.evaluationConnecting_natural X τ
    (M₁ := baseCokernelModule D hf (n+4)) (N₁ := termModule D hf (n+3))
    (P₁ := baseCokernelModule D hf (n+3))
    (M₂ := baseCokernelModule D hf (n+1)) (N₂ := termModule D hf n)
    (P₂ := baseCokernelModule D hf n)
    (baseStepInclusion D hex (n+3)) (LinearMap.range (D.d (n+3))).mkQ
    (baseStepInclusion D hex n) (LinearMap.range (D.d n)).mkQ
    (baseStepInclusion_injective D hex (n+3)) (Submodule.mkQ_surjective _) (baseStep_exact D hex (n+3))
    (baseStepInclusion_injective D hex n) (Submodule.mkQ_surjective _) (baseStep_exact D hex n)
    (secondCokernelMap D (n+1)) (D.second n) (secondCokernelMap D n)
    (secondCokernelMap_cover D hex n) (secondCokernelMap_quotient D n)
  simp only [evaluatedSecondCokernel, evaluatedBaseSuccessorIso,
    FiniteLeftModule.evaluationSuccessorIso_hom]
  convert! h using 1

def evaluatedBaseIteration (n : ℕ) : evaluatedBase D hf X τ 0 ≅
    (evaluatedBase D hf X τ n)⟦(n : ℤ)⟧ :=
  iteratedShiftIso (evaluatedBase D hf X τ)
    (evaluatedBaseSuccessorIso D hf hex hr hp X τ) n

def evaluatedCubicSourceIteration (n : ℕ) : evaluatedBase D hf X τ 3 ≅
    (evaluatedBase D hf X τ (n+3))⟦(n : ℤ)⟧ :=
  iteratedShiftIso (fun j => evaluatedBase D hf X τ (j+3))
    (fun j => evaluatedBaseSuccessorIso D hf hex hr hp X τ (j+3)) n

theorem evaluatedFirstCokernel_iterated (n : ℕ) :
    evaluatedFirstCokernel D hf X τ 0 ≫
      (evaluatedBaseIteration D hf hex hr hp X τ n).hom =
    (evaluatedCubicSourceIteration D hf hex hr hp X τ n).hom ≫
      (CategoryTheory.shiftFunctor HC (n : ℤ)).map
        (evaluatedFirstCokernel D hf X τ n) :=
  iteratedShiftIso_natural
    (Y := fun j => evaluatedBase D hf X τ (j+3))
    (s := fun j => evaluatedBaseSuccessorIso D hf hex hr hp X τ (j+3))
    (fun j => evaluatedBaseSuccessorIso D hf hex hr hp X τ j)
    (evaluatedFirstCokernel D hf X τ)
    (evaluatedFirstCokernel_step D hf hex hr hp X τ) n

theorem evaluatedSecondCokernel_iterated (n : ℕ) :
    evaluatedSecondCokernel D hf X τ 0 ≫
      (evaluatedBaseIteration D hf hex hr hp X τ n).hom =
    (evaluatedCubicSourceIteration D hf hex hr hp X τ n).hom ≫
      (CategoryTheory.shiftFunctor HC (n : ℤ)).map
        (evaluatedSecondCokernel D hf X τ n) :=
  iteratedShiftIso_natural
    (Y := fun j => evaluatedBase D hf X τ (j+3))
    (s := fun j => evaluatedBaseSuccessorIso D hf hex hr hp X τ (j+3))
    (fun j => evaluatedBaseSuccessorIso D hf hex hr hp X τ j)
    (evaluatedSecondCokernel D hf X τ)
    (evaluatedSecondCokernel_step D hf hex hr hp X τ) n

end ArExplicit.TwoCone

end

end OAI
