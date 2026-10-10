import Mathlib
import OAI.Analysis.Commutator.AtomicDecomposition
import OAI.Analysis.Commutator.AtomicFinite
import OAI.Analysis.Commutator.AtomicInfinite
import OAI.Analysis.Commutator.FiniteDimensionalMain
import OAI.Analysis.Commutator.ProperlyInfiniteMain

namespace OAI

noncomputable section

section

noncomputable section

open scoped InnerProductSpace

namespace Kadison

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem uniform_commutator_atomic_factor (P : VonNeumannAlgebra H)
    (hfac : FactorCorner.IsFactor P)
    (hatom : ¬DiffuseProjection.HasNoMinimalProjections P)
    (Y : H →L[ℂ] H) (h : ℕ)
    (X : Matrix (Fin h) (Fin h) (H →L[ℂ] H)) (hX : ∀ i j,X i j∈P) :
    ‖diagonalAmplification h Y*matrixOperator h X-
      matrixOperator h X*diagonalAmplification h Y‖ ≤
      9*commutatorSeminorm P Y*‖matrixOperator h X‖ := by
  obtain ⟨p,hp⟩ := AtomicFactor.exists_minimal_of_not_diffuse P hatom
  obtain ⟨D⟩ := AtomicFactor.exists_decomposition P hfac hp
  rcases finite_or_infinite D.I with hD|hD
  · let := hD
    let := D.finite_dimensional hp
    exact (uniform_commutator_finiteDimensional P Y h X hX).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by norm_num : (2:ℝ)≤9)
        (commutatorSeminorm_nonneg P Y)) (norm_nonneg _))
  · let := hD
    obtain ⟨s,t,hs,ht,hst⟩ := D.two_isometries
    exact uniform_commutator_of_two_isometries P s t hs ht hst Y h X hX

end Kadison

end

end
end

end OAI
