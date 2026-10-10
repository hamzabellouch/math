import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.CStarAlgebra.CStarMatrix

namespace OAI

noncomputable section

open scoped ComplexOrder

namespace Kaplansky

variable {A : Type*} [CStarAlgebra A]

structure OneQuasitrace (A : Type*) [CStarAlgebra A] where
  toFun : A → ℂ
  square_nonneg : ∀ x, 0 ≤ toFun (star x * x)
  square_swap : ∀ x, toFun (star x * x) = toFun (x * star x)
  real_imag : ∀ h k, IsSelfAdjoint h → IsSelfAdjoint k →
    toFun (h + Complex.I • k) = toFun h + Complex.I * toFun k
  abelian_linear : ∀ S : NonUnitalStarSubalgebra ℂ A,
    IsClosed (S : Set A) → (∀ x y : S, x * y = y * x) →
    ∃ f : S →ₗ[ℂ] ℂ, ∀ x : S, f x = toFun x

instance : CoeFun (OneQuasitrace A) (fun _ => A → ℂ) := ⟨OneQuasitrace.toFun⟩

def OneQuasitrace.Normalized (τ : OneQuasitrace A) : Prop := τ 1 = 1

attribute [local instance] CStarAlgebra.spectralOrder CStarAlgebra.spectralOrderedRing

def upperLeft (a : A) : CStarMatrix (Fin 2) (Fin 2) A :=
  CStarMatrix.ofMatrix fun i j => if i = 0 ∧ j = 0 then a else 0

def OneQuasitrace.IsTwo (τ : OneQuasitrace A) : Prop :=
  ∃ σ : OneQuasitrace (CStarMatrix (Fin 2) (Fin 2) A), ∀ a, σ (upperLeft a) = τ a

def PositiveContraction (a : A) : Prop := (∃ x, a = star x * x) ∧ ‖a‖ ≤ 1

def MainTarget : Prop :=
  ∃ (A : Type) (inst : CStarAlgebra A),
    letI := inst
    TopologicalSpace.SeparableSpace A ∧
    (∃ τ : OneQuasitrace A, τ.Normalized ∧ τ.IsTwo) ∧
    ∃ a b : A, PositiveContraction a ∧ PositiveContraction b ∧
      ∀ τ : OneQuasitrace A, τ.Normalized → τ.IsTwo →
        (1 : ℝ) / 144 ≤ (τ (a+b) - τ a - τ b).re

theorem kaplansky_quasitrace_counterexample : MainTarget := by
  sorry

end Kaplansky

end

end OAI
