import OAI.GroupTheory.PolycyclicRecognition.Geometry.PolynomialExponentialCoordinates

namespace OAI

/-! # Straight one-parameter subgroups in polynomial exponential coordinates -/

noncomputable section
namespace PolycyclicRecognition

open scoped Manifold

variable {L : Type*} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]
  [P : PolynomialExponentialCoordinates L]

theorem PolynomialExponentialCoordinates.axis_normalized (i : Fin 2) (v : L) :
    finiteDynkinPolynomial P.coefficients (Pi.single i v) = v := by
  fin_cases i
  · change finiteDynkinPolynomial P.coefficients (Pi.single (0 : Fin 2) v) = v
    have heq : (Pi.single (0 : Fin 2) v) = ![v, 0] := by
      ext j
      fin_cases j <;> simp
    rw [heq, ← P.mul_eq, ← P.one_eq_zero, mul_one]
  · change finiteDynkinPolynomial P.coefficients (Pi.single (1 : Fin 2) v) = v
    have heq : (Pi.single (1 : Fin 2) v) = ![0, v] := by
      ext j
      fin_cases j <;> simp
    rw [heq, ← P.mul_eq, ← P.one_eq_zero, one_mul]

theorem PolynomialExponentialCoordinates.smul_mul (v : L) (s t : ℝ) :
    (s • v) * (t • v) = (s + t) • v := by
  rw [P.mul_eq]
  have heq : (fun i : Fin 2 => ![s, t] i • v) = ![s • v, t • v] := by
    ext i
    fin_cases i <;> rfl
  have h := finiteDynkinPolynomial_collinear_eq_linear P.coefficients ![s, t] v
  rw [heq, binaryDynkinLinearPart P.coefficients
    (PolynomialExponentialCoordinates.axis_normalized)] at h
  exact h.trans (add_smul s t v).symm

theorem PolynomialExponentialCoordinates.isGroupExponential_identity :
    IsGroupExponential (fun x : GroupLieAlgebra (𝓘(ℝ, L)) L => (x : L)) := by
  refine ⟨P.one_eq_zero.symm, ?_, ?_⟩
  · intro v s t
    exact (PolynomialExponentialCoordinates.smul_mul (L := L) (v : L) s t).symm
  · intro v
    exact ((hasFDerivAt_id (𝕜 := ℝ) (0 : ℝ)).smul_const (show L from v)).hasMFDerivAt

end PolycyclicRecognition

end

end OAI
