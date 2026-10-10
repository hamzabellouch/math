import OAI.Algebra.AuslanderReiten.Cones.TwoConeModuleTriangles
import OAI.Algebra.AuslanderReiten.Coordinates.IteratedShiftNaturality

namespace OAI

noncomputable section
open CategoryTheory
open scoped ModuleCat.Algebra

namespace ArExplicit.TwoCone

universe u
variable {k R : Type u} [Field k] [Ring R] [Algebra k R] [Module.Finite k R]
variable (D : Data R) (hf : ∀ n, Module.Finite k (D.term n)) (τ : FrobeniusTrace k R)
variable (hex : ∀ n, Function.Exact (D.d (n + 1)) (D.d n))
variable (hp : ∀ n, Module.Projective R (D.term n))

abbrev baseResolution (n : ℕ) :=
  (HomotopyCategory.quotient (ModuleCat.{u} R) (ComplexShape.up ℤ)).obj
    ((baseCokernelModule D hf n).completeCochain τ)

def baseOffsetShiftIso (m n : ℕ) :
    baseResolution D hf τ m ≅ (baseResolution D hf τ (m + n))⟦(n : ℤ)⟧ :=
  iteratedShiftIso (fun j => baseResolution D hf τ (m + j))
    (fun j => baseSuccessorShiftIso D hf τ hex hp (m + j)) n

theorem baseIteratedShiftIso_eq_iterated (n : ℕ) :
    baseIteratedShiftIso D hf τ hex hp n =
      iteratedShiftIso (baseResolution D hf τ) (baseSuccessorShiftIso D hf τ hex hp) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    dsimp only [baseIteratedShiftIso, Nat.recAux, iteratedShiftIso] at *
    erw [ih]

variable (S : Data R) (hS : ∀ n, Module.Finite k (S.term n))
variable (eS : ∀ n, Function.Exact (S.d (n + 1)) (S.d n))
variable (pS : ∀ n, Module.Projective R (S.term n))
variable (m : ℕ)
variable (f : ∀ n, BaseCokernel S n →ₗ[R] BaseCokernel D (m + n))
variable (v : ∀ n, S.term n →ₗ[R] D.term (m + n))
variable (hv : ∀ n, (v n).comp (baseStepInclusion S eS n) =
  (baseStepInclusion D hex (m + n)).comp (f (n + 1)))
variable (hq : ∀ n, ((LinearMap.range (D.d (m + n))).mkQ).comp (v n) =
  (f n).comp (LinearMap.range (S.d n)).mkQ)

include v hv hq

theorem baseSuccessorShiftIso_natural (n : ℕ) :
    (HomotopyCategory.quotient _ _).map (FiniteLeftModule.resolutionMap τ
      (M := baseCokernelModule S hS n) (N := baseCokernelModule D hf (m + n)) (f n)) ≫
        (baseSuccessorShiftIso D hf τ hex hp (m + n)).hom =
      (baseSuccessorShiftIso S hS τ eS pS n).hom ≫
        (CategoryTheory.shiftFunctor (HomotopyCategory (ModuleCat.{u} R) (ComplexShape.up ℤ)) 1).map
          ((HomotopyCategory.quotient _ _).map (FiniteLeftModule.resolutionMap τ
            (M := baseCokernelModule S hS (n + 1))
            (N := baseCokernelModule D hf (m + (n + 1))) (f (n + 1)))) := by
  have h := FiniteLeftModule.resolutionConnecting_natural τ
    (M₁ := baseCokernelModule S hS (n + 1)) (N₁ := termModule S hS n)
    (L₁ := baseCokernelModule S hS n)
    (M₂ := baseCokernelModule D hf (m + (n + 1))) (N₂ := termModule D hf (m + n))
    (L₂ := baseCokernelModule D hf (m + n))
    (baseStepInclusion S eS n) (LinearMap.range (S.d n)).mkQ
    (baseStepInclusion D hex (m + n)) (LinearMap.range (D.d (m + n))).mkQ
    (baseStepInclusion_injective S eS n) (Submodule.mkQ_surjective _) (baseStep_exact S eS n)
    (baseStepInclusion_injective D hex (m + n)) (Submodule.mkQ_surjective _) (baseStep_exact D hex (m + n))
    (f (n + 1)) (v n) (f n) (hv n) (hq n)
  let := hp (m + n)
  let := pS n
  simpa only [baseSuccessorShiftIso, FiniteLeftModule.projectiveMiddleShiftIso_hom] using h

theorem baseIteratedShiftIso_natural (n : ℕ) :
    (HomotopyCategory.quotient _ _).map (FiniteLeftModule.resolutionMap τ
      (M := baseCokernelModule S hS 0) (N := baseCokernelModule D hf m) (f 0)) ≫
        (baseOffsetShiftIso D hf τ hex hp m n).hom =
      (baseIteratedShiftIso S hS τ eS pS n).hom ≫
        (CategoryTheory.shiftFunctor (HomotopyCategory (ModuleCat.{u} R) (ComplexShape.up ℤ)) (n : ℤ)).map
          ((HomotopyCategory.quotient _ _).map (FiniteLeftModule.resolutionMap τ
            (M := baseCokernelModule S hS n)
            (N := baseCokernelModule D hf (m + n)) (f n))) := by
  have h := iteratedShiftIso_natural
    (Y := baseResolution S hS τ) (s := baseSuccessorShiftIso S hS τ eS pS)
    (Z := fun j => baseResolution D hf τ (m + j))
    (fun j => baseSuccessorShiftIso D hf τ hex hp (m + j))
    (fun j => (HomotopyCategory.quotient _ _).map (FiniteLeftModule.resolutionMap τ
      (M := baseCokernelModule S hS j) (N := baseCokernelModule D hf (m + j)) (f j)))
    (baseSuccessorShiftIso_natural D hf τ hex hp S hS eS pS m f v hv hq) n
  simpa only [baseOffsetShiftIso, baseIteratedShiftIso_eq_iterated] using h

end ArExplicit.TwoCone

end

end OAI
