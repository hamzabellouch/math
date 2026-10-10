import OAI.Analysis.KadisonSimilarity.Tracial.FiniteFactorSymmetrization
import OAI.Analysis.KadisonSimilarity.Representation.FiniteAmplificationReduction

namespace OAI

/-! The finite type-I branch of the factor argument. Actual normalized
matrix-unitary averaging puts the operator within its scalar commutator
norm of the commutant, giving complete commutator constant two. -/

noncomputable section
namespace KadisonSimilarity

variable {H α : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [Fintype α] [DecidableEq α] [Nonempty α]

/-- A represented full finite matrix algebra has the uniform matrix
commutator estimate with constant two, in every multiplicity. -/
theorem finiteTypeI_commutator_estimate (P : VonNeumannAlgebra H)
    (ι : Matrix α α ℂ →⋆ₐ[ℂ] (H →L[ℂ] H))
    (hmem : ∀ a, ι a ∈ P)
    (hsurj : ∀ T : H →L[ℂ] H, T ∈ P → ∃ a, ι a = T) :
    CommutatorEstimate P 2 := by
  intro Y n X hX
  obtain ⟨Y₀, _hnorm, hclose, _hscalar, hinv⟩ :=
    exists_finite_matrix_symmetrization (I := fun _ : ℕ => α) P (fun _ => ι)
      (fun _ => hmem) (fun _ _ _ => StarAlgHom.id ℂ (Matrix α α ℂ))
      (fun _ _ _ _ => rfl) Y
  have hcomm (i j : Fin n) : commutator Y₀ (X i j) = 0 := by
    obtain ⟨a, ha⟩ := hsurj (X i j) (hX i j)
    rw [← ha]
    exact hinv 0 a
  have hz : commutator (amplify Y₀ n) (matrixOperator X) = 0 := by
    rw [commutator_amplify_matrixOperator]
    ext ξ i
    simp [matrixOperator, hcomm]
  have hc : ‖amplify Y n - amplify Y₀ n‖ ≤ scalarCommutatorNorm P Y := by
    apply (norm_amplify_sub_le Y Y₀ n).trans
    rwa [norm_sub_rev]
  have h := norm_commutator_le_of_approx (amplify Y n) (amplify Y₀ n) (matrixOperator X)
    (show ‖commutator (amplify Y₀ n) (matrixOperator X)‖ ≤ 0 by rw [hz, norm_zero]) hc
  simpa only [zero_add] using h

end KadisonSimilarity

end

end OAI
