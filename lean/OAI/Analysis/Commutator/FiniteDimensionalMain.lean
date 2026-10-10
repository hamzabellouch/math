import Mathlib
import OAI.Analysis.Commutator.FiniteDimensionalAverage
import OAI.Analysis.Commutator.MainCommutantDistance

namespace OAI

noncomputable section

section

noncomputable section

open scoped InnerProductSpace

universe u

namespace Kadison

variable {K : Type u} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

theorem uniform_commutator_finiteDimensional
    (P : VonNeumannAlgebra K) [FiniteDimensional ℂ P]
    (Y : K →L[ℂ] K) (h : ℕ)
    (X : Matrix (Fin h) (Fin h) (K →L[ℂ] K)) (hX : ∀ i j,X i j∈P) :
    ‖diagonalAmplification h Y*matrixOperator h X-matrixOperator h X*diagonalAmplification h Y‖ ≤
      2*commutatorSeminorm P Y*‖matrixOperator h X‖ := by
  obtain ⟨Y₀,hcomm,hnear⟩ := finiteDimensional_commutant_approximation P Y
  exact matrix_commutator_bound_of_commutant_approximation P Y Y₀ hnear hcomm h X hX

end Kadison

end

end
end

end OAI
