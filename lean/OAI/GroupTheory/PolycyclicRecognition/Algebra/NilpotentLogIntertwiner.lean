import OAI.GroupTheory.PolycyclicRecognition.Algebra.CanonicalNilpotentLogarithm
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

namespace OAI

/-! # Finite logarithms preserve linear intertwiners -/

noncomputable section
namespace PolycyclicRecognition
variable {𝕜 V W : Type*} [Field 𝕜] [AddCommGroup V] [Module 𝕜 V]
  [AddCommGroup W] [Module 𝕜 W]

theorem end_polynomial_intertwiner (f : V →ₗ[𝕜] W)
    (A : Module.End 𝕜 V) (B : Module.End 𝕜 W)
    (h : ∀ x, f (A x) = B (f x)) (p : Polynomial 𝕜) (x : V) :
    f (Polynomial.aeval A p x) = Polynomial.aeval B p (f x) := by
  have hp (n : ℕ) (y : V) : f ((A ^ n) y) = (B ^ n) (f y) := by
    induction n with
    | zero => rfl
    | succ n ih => simp only [pow_succ', Module.End.mul_apply, h, ih]
  induction p using Polynomial.induction_on' with
  | add p q ihp ihq => simp only [map_add, LinearMap.add_apply, ihp, ihq]
  | monomial n r =>
    simp only [Polynomial.aeval_monomial, Module.End.mul_apply,
      Algebra.algebraMap_eq_smul_one, LinearMap.smul_apply, Module.End.one_apply,
      map_smul, hp]

variable {V W : Type*} [AddCommGroup V] [Module ℚ V] [AddCommGroup W] [Module ℚ W]

theorem nilpotentLog_intertwiner (f : V →ₗ[ℚ] W)
    (A : Module.End ℚ V) (B : Module.End ℚ W)
    (hA : IsNilpotent A) (hB : IsNilpotent B)
    (h : ∀ x, f (A x) = B (f x)) (x : V) :
    f (nilpotentLog A x) = nilpotentLog B (f x) := by
  let n := max (nilpotencyClass A) (nilpotencyClass B)
  have ha : A ^ (n + 1) = 0 := pow_eq_zero_of_le (by omega) (pow_nilpotencyClass hA)
  have hb : B ^ (n + 1) = 0 := pow_eq_zero_of_le (by omega) (pow_nilpotencyClass hB)
  rw [nilpotentLog_eq_of_pow A hA n ha, nilpotentLog_eq_of_pow B hB n hb]
  exact end_polynomial_intertwiner f A B h _ x

end PolycyclicRecognition

end

end OAI
