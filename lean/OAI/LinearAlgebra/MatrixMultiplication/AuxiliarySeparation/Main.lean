import OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Arithmetic.Exponent
import OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Arithmetic.RankBound
import OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Convolution.RankLowerBound
import OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Determinant.Bounds
import OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Growth.Floor

namespace OAI

/-!
# Matrix multiplication via auxiliary separation and polynomial multiplication

Theorem 1.1 gives a uniform arithmetic-operation bound for complex square
matrix multiplication, and consequently an upper bound of `9/4` on its exponent.
The two conclusions are stated separately in the existing arithmetic model.
-/

namespace MatrixMultiplication.AuxiliarySeparation

/-- Theorem 1.1: for every positive exponent slack, one constant bounds the cost
of correct complex matrix multiplication programs at every positive size. -/
theorem matrix_multiplication_cost_le (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n →
      ∃ P : Arithmetic.MatrixAlgorithm ℂ n n n,
        P.Correct ∧ (P.cost : ℝ) ≤ C * (n : ℝ) ^ ((9 : ℝ) / 4 + ε) :=
  arithmeticComplexity_of_exactRankExponent_le exactRankExponent_le_nine_quarters ε hε

/-- The complex arithmetic matrix multiplication exponent is at most `9/4`. -/
theorem omega_le_nine_quarters : Arithmetic.omega ℂ ≤ (9 : ℝ) / 4 :=
  omega_le_exactRankExponent.trans exactRankExponent_le_nine_quarters

end MatrixMultiplication.AuxiliarySeparation

end OAI
