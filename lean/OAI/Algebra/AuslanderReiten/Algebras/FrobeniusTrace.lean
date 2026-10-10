import OAI.Algebra.AuslanderReiten.Modules.Coinduced
import OAI.Algebra.AuslanderReiten.Algebras.TrivialExtension
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

namespace OAI

namespace ArExplicit

structure FrobeniusTrace (k R : Type*) [Field k] [Ring R] [Algebra k R] where
  trace : R →ₗ[k] k
  separates : ∀ a : R, (∀ b : R, trace (b * a) = 0) → a = 0

namespace FrobeniusTrace

variable {k R : Type*} [Field k] [Ring R] [Algebra k R] (τ : FrobeniusTrace k R)

theorem leftMap_injective : Function.Injective (Coinduced.fromFunctional τ.trace) := by
  intro x y h
  apply sub_eq_zero.mp
  apply τ.separates
  intro b
  rw [mul_sub, map_sub, sub_eq_zero]
  exact congrArg (fun a : Coinduced k R => a.functional b) h

variable [Module.Finite k R]

noncomputable def leftEquiv : R ≃ₗ[R] Coinduced k R := by
  have hi := τ.leftMap_injective
  have hs : Function.Surjective ((Coinduced.fromFunctional τ.trace).restrictScalars k) :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (Coinduced.finrank_eq (k := k) (R := R)).symm).mp hi
  exact LinearEquiv.ofBijective (Coinduced.fromFunctional τ.trace) ⟨hi, hs⟩

@[simp] theorem leftEquiv_apply (a b : R) :
    (τ.leftEquiv a).functional b = τ.trace (b * a) := rfl

noncomputable def dualEquiv : R ≃ₗ[k] Module.Dual k R :=
  (τ.leftEquiv.restrictScalars k).trans Coinduced.scalarLinearEquiv

@[simp] theorem dualEquiv_apply (a b : R) : τ.dualEquiv a b = τ.trace (b * a) := rfl

include τ in

theorem regular_injective : Module.Injective R R :=
  Module.Baer.injective <| Module.Baer.of_equiv τ.leftEquiv.symm
    (Module.Baer.of_injective (inferInstance : Module.Injective R (Coinduced k R)))

end FrobeniusTrace

def trivialExtensionFrobeniusTrace (k R : Type*) [Field k] [Ring R] [Algebra k R] :
    FrobeniusTrace k (TrivialExtension k R) where
  trace := TrivialExtension.trace
  separates a h := (TrivialExtension.traceForm_nondegenerate (k := k) (A := R)).2 a h

end ArExplicit

end OAI
