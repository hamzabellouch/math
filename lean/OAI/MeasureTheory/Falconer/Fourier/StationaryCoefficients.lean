import OAI.MeasureTheory.Falconer.Fourier.QuadraticStationary
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Algebra.Hom

namespace OAI

/-!
# Identification of the outgoing stationary coefficients

The zeroth coefficient is evaluated on the chart amplitude.
The outgoing Helmholtz recurrence uniquely determines the manuscript's
polynomial coefficients. The identification for local quadratic jets is
conditional on their satisfying this recurrence.
-/

namespace Falconer
open Polynomial

@[simp] theorem quadraticAmplitude_zero (m : ℕ) (b : Sphere (m+3) → ℂ) :
    quadraticAmplitude m b 0 = b (gnomonicChart 0) := by
  simp [quadraticAmplitude, quadraticToGnomonic]

@[simp] theorem quadraticJetCoefficient_amplitude_zero
    (m : ℕ) (b : Sphere (m+3) → ℂ) :
    quadraticJetCoefficient 0 (quadraticAmplitude m b) =
      sphereStationaryConstant (m+2) * b (gnomonicChart 0) := by
  rw [quadraticJetCoefficient_zero, quadraticAmplitude_zero]

section Operators
variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- Evaluation of the exact direct polynomial at a linear angular operator. -/
noncomputable def sphereDirectOperator (D : Module.End ℂ V) (n j : ℕ) : Module.End ℂ V :=
  aeval D (sphereDirectPolynomial n j)

@[simp] theorem sphereDirectOperator_zero (D : Module.End ℂ V) (n : ℕ) (b : V) :
    sphereDirectOperator D n 0 b = sphereStationaryConstant n • b := by
  simp [sphereDirectOperator, Module.algebraMap_end_apply]

theorem sphereDirectOperator_recurrence (D : Module.End ℂ V) (n j : ℕ) (b : V) :
    (2 * Complex.I * (j+1)) • sphereDirectOperator D n (j+1) b =
      D (sphereDirectOperator D n j b) +
        ((j : ℂ)*(j+1) - (n : ℂ)*((n : ℂ)-2)/4) • sphereDirectOperator D n j b := by
  have hp := congrArg (fun P : Polynomial ℂ => (aeval D P) b)
    (sphereDirectPolynomial_succ n j)
  simpa only [map_mul, map_add, aeval_C, aeval_X, Module.End.mul_apply,
    Module.algebraMap_end_apply, LinearMap.add_apply, sphereDirectOperator,
    mul_smul, add_smul, smul_add, one_smul] using hp

/-- Once the genuine outgoing coefficients satisfy the Helmholtz recurrence,
their identification with `L_j` is forced; no arbitrary choice of higher
coefficients remains. -/
theorem sphereDirectOperator_unique (D : Module.End ℂ V) (n : ℕ) (b : V)
    (a : ℕ → V) (hzero : a 0 = sphereStationaryConstant n • b)
    (hrec : ∀ j : ℕ, (2 * Complex.I * (j+1)) • a (j+1) =
      D (a j) + ((j : ℂ)*(j+1) - (n : ℂ)*((n : ℂ)-2)/4) • a j) :
    ∀ j, a j = sphereDirectOperator D n j b := by
  intro j
  induction j with
  | zero => simpa using hzero
  | succ j hj =>
      have hz : (2 * Complex.I * (j+1) : ℂ) ≠ 0 := by
        apply mul_ne_zero (mul_ne_zero (by norm_num) Complex.I_ne_zero)
        exact_mod_cast (show j+1 ≠ 0 by omega)
      apply (smul_right_injective V hz)
      change (2 * Complex.I * (j+1)) • a (j+1) =
        (2 * Complex.I * (j+1)) • sphereDirectOperator D n (j+1) b
      rw [hrec j, sphereDirectOperator_recurrence, hj]

end Operators
end Falconer

end OAI
