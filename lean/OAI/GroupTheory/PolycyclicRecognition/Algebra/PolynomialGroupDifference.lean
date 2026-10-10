import OAI.GroupTheory.PolycyclicRecognition.Geometry.PolynomialModelExponential
import OAI.GroupTheory.PolycyclicRecognition.Algebra.DynkinFiniteDifference

namespace OAI

/-! # A finite-difference estimate for the polynomial nilpotent group law -/

noncomputable section
namespace PolycyclicRecognition
open LieModule
variable {L : Type} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]
  [P : PolynomialExponentialCoordinates L]

theorem polynomial_mul_difference (k : ℕ) (a b c d : L)
    (hac : a - c ∈ lowerCentralSeries ℝ L L k)
    (hbd : b - d ∈ lowerCentralSeries ℝ L L k) :
    ((a * b) - (c * d)) - ((a - c) + (b - d)) ∈
      (lowerCentralSeries ℝ L L (k + 1)).toSubmodule := by
  have h := finiteDynkinPolynomial_sub_linear_mem_succ P.coefficients ![a, b] ![c, d] k (by
    intro i
    fin_cases i
    · exact hac
    · exact hbd)
  have he : ![a, b] - ![c, d] = ![a - c, b - d] := by
    ext i
    fin_cases i <;> rfl
  rw [he, binaryDynkinLinearPart P.coefficients
    (PolynomialExponentialCoordinates.axis_normalized), ← P.mul_eq, ← P.mul_eq] at h
  exact h

end PolycyclicRecognition

end

end OAI
