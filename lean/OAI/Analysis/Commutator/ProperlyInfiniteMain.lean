import Mathlib
import OAI.Analysis.Commutator.ProperlyInfiniteBound
import OAI.Analysis.Commutator.TwoIsometries

namespace OAI

noncomputable section

section

noncomputable section

open scoped InnerProductSpace

universe u

namespace Kadison

variable {K : Type u} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

theorem uniform_commutator_of_two_isometries
    (P : VonNeumannAlgebra K) (s t : P)
    (hs : star s*s=1) (ht : star t*t=1) (hst : star s*t=0)
    (Y : K →L[ℂ] K) (h : ℕ)
    (X : Matrix (Fin h) (Fin h) (K →L[ℂ] K)) (hX : ∀ i j,X i j∈P) :
    ‖diagonalAmplification h Y*matrixOperator h X-matrixOperator h X*diagonalAmplification h Y‖ ≤
      9*commutatorSeminorm P Y*‖matrixOperator h X‖ := by
  obtain ⟨v,hv⟩ := two_isometries_finite_family s t hs ht hst h
  exact uniform_commutator_of_isometries P Y h v hv X hX

end Kadison

end

end
end

end OAI
