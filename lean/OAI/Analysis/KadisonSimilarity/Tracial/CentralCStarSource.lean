import OAI.Analysis.KadisonSimilarity.Representation.CountablyGeneratedCStarAlgebra
import OAI.Analysis.KadisonSimilarity.Representation.CentralDecomposition

namespace OAI

/-! A norm-separable commutative C-star source for the center. Its commutant
is the full central commutant, so its common spectral fields apply to every
operator required by the central-decomposition estimate. -/

noncomputable section
namespace KadisonSimilarity

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Every star subalgebra of the center is commutative. -/
theorem central_subalgebra_isMulCommutative (P : VonNeumannAlgebra H)
    (A : StarSubalgebra ℂ (H →L[ℂ] H)) (hA : A ≤ (vonNeumannCenter P).toStarSubalgebra) :
    IsMulCommutative A := by
  apply IsMulCommutative.of_setLike_mul_comm
  intro x hx y hy
  exact (VonNeumannAlgebra.mem_commutant_iff.mp (hA hy).2) x (hA hx).1

/-- The source inclusion has exactly its original star subalgebra as range. -/
theorem subtype_star_range (A : StarSubalgebra ℂ (H →L[ℂ] H)) :
    A.subtype.range = A := by
  ext x
  constructor
  · rintro ⟨a, rfl⟩
    exact a.property
  · intro hx
    exact ⟨⟨x, hx⟩, rfl⟩

/-- A weakly generating central source has the full central commutant. -/
theorem central_source_commutant (P : VonNeumannAlgebra H)
    (A : StarSubalgebra ℂ (H →L[ℂ] H))
    (hgen : (starSubalgebraCommutant A).commutant = vonNeumannCenter P) :
    starSubalgebraCommutant A = (vonNeumannCenter P).commutant := by
  have h := congrArg VonNeumannAlgebra.commutant hgen
  simpa only [VonNeumannAlgebra.commutant_commutant] using h

/-- Choose only a norm-separable source; the center itself need not be
norm separable. -/
theorem exists_separable_central_source [TopologicalSpace.SeparableSpace H]
    (P : VonNeumannAlgebra H) :
    ∃ A : StarSubalgebra ℂ (H →L[ℂ] H),
      IsClosed (A : Set (H →L[ℂ] H)) ∧ TopologicalSpace.SeparableSpace A ∧
      IsMulCommutative A ∧ A ≤ (vonNeumannCenter P).toStarSubalgebra ∧
      starSubalgebraCommutant A = (vonNeumannCenter P).commutant := by
  obtain ⟨A, hclosed, hsep, hA, hgen⟩ :=
    exists_separable_generating_cstar_subalgebra (vonNeumannCenter P)
  exact ⟨A, hclosed, hsep, central_subalgebra_isMulCommutative P A hA, hA,
    central_source_commutant P A hgen⟩

end KadisonSimilarity

end

end OAI
