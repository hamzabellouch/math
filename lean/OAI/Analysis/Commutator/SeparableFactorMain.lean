import Mathlib
import OAI.Analysis.Commutator.AtomicFactorMain
import OAI.Analysis.Commutator.FiniteFactorTrace
import OAI.Analysis.Commutator.NonfiniteFactor
import OAI.Analysis.Commutator.TracedSeparableFactorMain

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder InnerProductSpace

namespace Kadison

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H]

theorem uniform_commutator_separable_factor (P : VonNeumannAlgebra H)
    (hfac : FactorCorner.IsFactor P) (Y : H →L[ℂ] H) (h : ℕ) (hh : 1≤h)
    (X : Matrix (Fin h) (Fin h) (H →L[ℂ] H)) (hX : ∀ i j,X i j∈P) :
    ‖diagonalAmplification h Y*matrixOperator h X-
      matrixOperator h X*diagonalAmplification h Y‖ ≤
      3122*commutatorSeminorm P Y*‖matrixOperator h X‖ := by
  classical
  rcases subsingleton_or_nontrivial H with hH|hH
  · let := hH
    have hz : diagonalAmplification h Y*matrixOperator h X-
      matrixOperator h X*diagonalAmplification h Y=0 := by
      ext x i
      exact Subsingleton.elim _ _
    rw [hz,norm_zero]
    exact mul_nonneg (mul_nonneg (by norm_num) (commutatorSeminorm_nonneg P Y)) (norm_nonneg _)
  · let := hH
    have hc : 9*commutatorSeminorm P Y*‖matrixOperator h X‖≤
        3122*commutatorSeminorm P Y*‖matrixOperator h X‖ :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by norm_num : (9:ℝ)≤3122)
        (commutatorSeminorm_nonneg P Y)) (norm_nonneg _)
    by_cases hd : DiffuseProjection.HasNoMinimalProjections P
    · by_cases hf : PartialIsometryOrder.IsFiniteAlgebra P
      · obtain ⟨τ,htr,hnormal,hfaith,hone⟩ :=
          OrbitStateHull.exists_faithful_normal_trace P hfac hd hf
        exact NormalRepresentation.separable_traced_factor_bound P τ htr hnormal hfaith hone
          hfac hd h hh Y X hX
      · exact (uniform_commutator_nonfinite_factor P hfac hf Y h X hX).trans hc
    · exact (uniform_commutator_atomic_factor P hfac hd Y h X hX).trans hc

end Kadison

end

end
end

end OAI
