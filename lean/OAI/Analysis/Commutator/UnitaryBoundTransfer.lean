import Mathlib
import OAI.Analysis.Commutator.UnitaryMainTransport

namespace OAI

noncomputable section

section

noncomputable section

namespace Kadison.UnitaryTransport

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

theorem bound_of_conjugate_bound (U : H ≃ₗᵢ[ℂ] K) (M : VonNeumannAlgebra H)
    (Y : H →L[ℂ] H) (h : ℕ) (X : Matrix (Fin h) (Fin h) (H →L[ℂ] H)) (c : ℝ)
    (hb : ‖diagonalAmplification h (U.conjStarAlgEquiv Y)*
      matrixOperator h (fun i j => U.conjStarAlgEquiv (X i j))-
      matrixOperator h (fun i j => U.conjStarAlgEquiv (X i j))*
      diagonalAmplification h (U.conjStarAlgEquiv Y)‖≤
      c*commutatorSeminorm (algebra U M) (U.conjStarAlgEquiv Y)*
      ‖matrixOperator h (fun i j => U.conjStarAlgEquiv (X i j))‖) :
    ‖diagonalAmplification h Y*matrixOperator h X-matrixOperator h X*diagonalAmplification h Y‖≤
      c*commutatorSeminorm M Y*‖matrixOperator h X‖ := by
  simpa only [matrix_commutator_norm,seminorm,matrix_norm] using hb

end Kadison.UnitaryTransport

end

end
end

end OAI
