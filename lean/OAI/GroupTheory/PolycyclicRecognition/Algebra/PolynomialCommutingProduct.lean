import OAI.GroupTheory.PolycyclicRecognition.Geometry.PolynomialModelExponential
import Mathlib.GroupTheory.Subgroup.Center

namespace OAI

/-! # Products of commuting logarithms

The finite BCH law is addition when the two logarithms have zero bracket.
-/

noncomputable section
namespace PolycyclicRecognition
variable {L : Type*} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]
  [P : PolynomialExponentialCoordinates L]

theorem polynomial_mul_eq_add_of_lie_eq_zero (x y : L) (hxy : ⁅x, y⁆ = 0) :
    x * y = x + y := by
  have hp (i j : Fin 2) : ⁅![x, y] i, ![x, y] j⁆ = 0 := by
    fin_cases i <;> fin_cases j
    · exact lie_self x
    · exact hxy
    · change ⁅y, x⁆ = 0
      rw [← lie_skew, hxy, neg_zero]
    · exact lie_self y
  have hw (d : ℕ) (w : Fin (d + 2) → Fin 2) :
      evalBracketWord ![x, y] (rightNestedWord (d + 1) w) = 0 := by
    induction d with
    | zero => exact hp (w 0) (w 1)
    | succ d ih =>
      change ⁅![x, y] (w 0),
        evalBracketWord ![x, y] (rightNestedWord (d + 1) (fun i => w i.succ))⁆ = 0
      rw [ih, lie_zero]
  have he (d : ℕ) (w : Fin (d + 1) → Fin 2) :
      evalBracketWord ![x, y] (rightNestedWord d w) =
        wordLinearPart (rightNestedWord d w) ![x, y] := by
    cases d with
    | zero => rfl
    | succ d => rw [hw]; rfl
  rw [P.mul_eq]
  have hlin : finiteDynkinPolynomial P.coefficients ![x, y] =
      finiteDynkinLinearPart P.coefficients ![x, y] := by
    simp only [finiteDynkinPolynomial, finiteDynkinLinearPart, LinearMap.sum_apply,
      LinearMap.smul_apply, he]
  rw [hlin, binaryDynkinLinearPart P.coefficients
    PolynomialExponentialCoordinates.axis_normalized]

theorem polynomial_mem_center_of_lie_eq_zero (x : L) (hx : ∀ y : L, ⁅x, y⁆ = 0) :
    x ∈ Subgroup.center L := by
  apply Subgroup.mem_center_iff.mpr
  intro y
  have hyx : ⁅y, x⁆ = 0 := by rw [← lie_skew, hx y, neg_zero]
  rw [polynomial_mul_eq_add_of_lie_eq_zero _ _ (hx y),
    polynomial_mul_eq_add_of_lie_eq_zero _ _ hyx, add_comm]

end PolycyclicRecognition

end

end OAI
