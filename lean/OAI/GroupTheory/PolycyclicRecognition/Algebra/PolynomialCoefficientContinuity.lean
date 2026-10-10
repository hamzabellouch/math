import OAI.GroupTheory.PolycyclicRecognition.Algebra.PolynomialFamilies
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.LinearAlgebra.Dual.Lemmas

namespace OAI

/-! # Coefficients of a continuous bounded-degree polynomial family

Each coefficient is a fixed finite linear combination of evaluations on
the finite-dimensional space of bounded-degree polynomials. This supplies
uniform coefficient bounds from compact parameter sets, even when the
input cubes have growing radii.
-/

noncomputable section
namespace PolycyclicRecognition

open Module MvPolynomial

def boundedDegreeEvaluation {m : ℕ} (D : ℕ) (x : Fin m → ℝ) :
    restrictTotalDegree (Fin m) ℝ D →ₗ[ℝ] ℝ :=
  (aeval x).toLinearMap.comp (restrictTotalDegree (Fin m) ℝ D).subtype

theorem boundedDegreeCoefficient_mem_span_evaluations {m : ℕ}
    (D : ℕ) (s : Fin m →₀ ℕ) :
    (lcoeff ℝ s).comp (restrictTotalDegree (Fin m) ℝ D).subtype ∈
      Submodule.span ℝ (Set.range (boundedDegreeEvaluation (m := m) D)) := by
  apply FiniteDimensional.mem_span_of_iInf_ker_le_ker
  intro p hp
  have he (x : Fin m → ℝ) : eval x p.val = 0 := by
    have hx := (Submodule.mem_iInf _).mp hp x
    exact hx
  have hz : p.val = 0 := MvPolynomial.funext (fun x => by simpa using he x)
  change p.val.coeff s = 0
  rw [hz]
  rfl

theorem continuous_polynomial_coefficients {P : Type*} [TopologicalSpace P] {m : ℕ}
    (p : P → MvPolynomial (Fin m) ℝ) (D : ℕ)
    (hD : ∀ a, (p a).totalDegree ≤ D)
    (heval : ∀ x : Fin m → ℝ, Continuous (fun a => eval x (p a)))
    (s : Fin m →₀ ℕ) : Continuous (fun a => (p a).coeff s) := by
  classical
  obtain ⟨t, ht⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp
    (boundedDegreeCoefficient_mem_span_evaluations D s)
  have hrep (a : P) : (p a).coeff s =
      ∑ x ∈ t.support, t x * eval x (p a) := by
    have hp : p a ∈ restrictTotalDegree (Fin m) ℝ D :=
      (mem_restrictTotalDegree _ _ _).mpr (hD a)
    have h := congrArg (fun L : restrictTotalDegree (Fin m) ℝ D →ₗ[ℝ] ℝ => L ⟨p a, hp⟩) ht
    simpa [Finsupp.linearCombination_apply, Finsupp.sum, boundedDegreeEvaluation] using h.symm
  simp_rw [hrep]
  apply continuous_finsetSum
  intro x _
  exact continuous_const.mul (heval x)

end PolycyclicRecognition

end

end OAI
