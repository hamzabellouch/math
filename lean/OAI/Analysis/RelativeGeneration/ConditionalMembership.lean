import OAI.Analysis.FactorGeneration.RelativeGeneration

namespace OAI

noncomputable section

namespace Generator.Tracial
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M)

/-- This is the actual bounded conditional-expectation step, including faithfulness. -/
theorem mem_subalgebra_of_baseVector_mem {Q : VonNeumannAlgebra H}
    (hQM : Q ≤ M) (x : M.toStarSubalgebra)
    (hx : baseVector τ x ∈ vectorOrbitClosure Q.toStarSubalgebra τ.vector) :
    x.val ∈ Q := by
  have hv := (vectorOrbitClosure Q.toStarSubalgebra τ.vector).starProjection_eq_self_iff.mpr hx
  rw [conditionalExpectation_vector_projection τ hQM x] at hv
  have he : conditionalExpectation τ hQM x = x := baseVector_injective τ hv
  exact he ▸ conditionalExpectation_mem τ hQM x

end Generator.Tracial

end

end OAI
