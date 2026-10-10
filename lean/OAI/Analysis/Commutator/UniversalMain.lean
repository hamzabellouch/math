import Mathlib
import OAI.Analysis.Commutator.StableUniversalAssembly

namespace OAI

noncomputable section

section

noncomputable section

universe u

namespace Kadison

theorem uniform_commutator :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (K : Type u) [NormedAddCommGroup K] [InnerProductSpace ℂ K]
      [CompleteSpace K] (P : VonNeumannAlgebra K) (Y : K →L[ℂ] K)
      (h : ℕ), 1 ≤ h → ∀ (X : Matrix (Fin h) (Fin h) (K →L[ℂ] K)),
      (∀ i j, X i j ∈ P) →
      ‖diagonalAmplification h Y * matrixOperator h X -
        matrixOperator h X * diagonalAmplification h Y‖ ≤
        C * commutatorSeminorm P Y * ‖matrixOperator h X‖ := by
  refine ⟨9368,by norm_num,?_⟩
  intro K _ _ _ P Y h hh X hX
  exact CentralSpectral.universal_bound P Y h hh X hX

end Kadison

end

end
end

end OAI
