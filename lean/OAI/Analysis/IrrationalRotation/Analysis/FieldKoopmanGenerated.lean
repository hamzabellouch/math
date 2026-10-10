import OAI.Analysis.IrrationalRotation.Rotation.FieldKoopmanDiagonal
import OAI.Analysis.IrrationalRotation.Analysis.GeneratedVonNeumann

namespace OAI

namespace Invariant233.FieldKoopman
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem commute_star_left_of_unitary {A J : H →L[ℂ] H}
    (hJ : J ∈ unitary (H →L[ℂ] H)) (h : Commute A J) : Commute (star A) J := by
  apply Commute.symm
  apply (commute_unitary_iff_star_left_conjugate hJ).mpr
  have heq := congrArg star ((commute_unitary_iff_star_left_conjugate hJ).mp h.symm)
  simpa only [star_mul, star_star, mul_assoc] using heq

theorem commute_of_mem_generated_of_unitary
    (s : Set (H →L[ℂ] H)) {J : H →L[ℂ] H}
    (hJ : J ∈ unitary (H →L[ℂ] H))
    (hs : ∀ A ∈ s, Commute A J) {T : H →L[ℂ] H}
    (hT : T ∈ vonNeumannGenerated s) : Commute T J := by
  have hmem : J ∈ (vonNeumannGenerated s).commutant := by
    apply (mem_commutant_vonNeumannGenerated_iff s J).mpr
    intro A hA
    exact ⟨(hs A hA).eq, (commute_star_left_of_unitary hJ (hs A hA)).eq⟩
  change T * J = J * T
  exact (VonNeumannAlgebra.mem_commutant_iff.mp hmem) T hT

end Invariant233.FieldKoopman

end OAI
