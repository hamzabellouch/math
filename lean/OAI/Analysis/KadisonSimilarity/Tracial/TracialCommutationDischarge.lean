import OAI.Analysis.KadisonSimilarity.Tracial.TracialCommutantTrace

namespace OAI

/-! The finite tracial commutation theorem for the given faithful normal
representation, using the constructed trace-preserving expectation. -/

noncomputable section
namespace KadisonSimilarity
open Generator.Tracial UltrapowerBridge
namespace TracialCornerGeometry

variable {P H : Type*} [CStarAlgebra P]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (G : TracialCornerGeometry P H)
  (h1 : G.trace 1 = 1) (hf : Function.Injective G.vector)
  (M : VonNeumannAlgebra H) (hrange : G.left.range = M.toStarSubalgebra)

include h1 M hrange in
theorem tracialCommutationInput_of_normal_range :
    TracialCommutationInput G.left (G.faithfulRightAction hf) := by
  let N := representationVonNeumannAlgebra G.rightRepresentation
  have hright : G.rightRepresentation.range = N.toStarSubalgebra :=
    G.rightRepresentation_normal_range h1 hf M hrange
  have hNM : N ≤ G.leftCommutant := by
    intro T hT
    change T ∈ N.toStarSubalgebra at hT
    rw [← hright] at hT
    obtain ⟨a, rfl⟩ := hT
    exact (G.mem_leftCommutant_iff _).mpr (fun b => G.right_left b (MulOpposite.unop a))
  let τ := G.commutantTracialRepresentation h1
  have hsub : Set.range G.vector ⊆ subalgebraTraceVectors τ N := by
    rintro _ ⟨a, rfl⟩
    have haN : G.right a ∈ N :=
      mem_representationVonNeumannAlgebra G.rightRepresentation (MulOpposite.op a)
    refine ⟨⟨G.right a, hNM haN⟩, haN, ?_⟩
    change G.right a (G.vector 1) = G.vector a
    rw [G.right_vector, one_mul]
  intro Z hZ
  have hZM : Z ∈ G.leftCommutant := (G.mem_leftCommutant_iff Z).mpr hZ
  have hZN : Z ∈ N := mem_of_traceVector_mem_closure τ hNM ⟨Z, hZM⟩
    (closure_mono hsub (G.dense_vector (Generator.Tracial.baseVector τ ⟨Z, hZM⟩)))
  change Z ∈ N.toStarSubalgebra at hZN
  rw [← hright] at hZN
  obtain ⟨a, ha⟩ := hZN
  exact ⟨MulOpposite.unop a, ha⟩

end TracialCornerGeometry
end KadisonSimilarity

end

end OAI
