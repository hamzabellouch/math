import OAI.Analysis.IrrationalRotation.Model.ConcreteSpectral
import OAI.Analysis.IrrationalRotation.Analysis.GeneratedVonNeumann
import OAI.Analysis.IrrationalRotation.Operators.CommutantProper

namespace OAI

open scoped Pointwise

namespace Invariant233

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

theorem mem_vonNeumannGenerated_empty_iff_scalar (T : H →L[ℂ] H) :
    T ∈ vonNeumannGenerated (∅ : Set (H →L[ℂ] H)) ↔
      ∃ c : ℂ, T = c • (1 : H →L[ℂ] H) := by
  rw [← centralizer_singleton_eq_top_iff_scalar]
  change T ∈ (vonNeumannGenerated (∅ : Set (H →L[ℂ] H)) : Set _) ↔ _
  rw [coe_vonNeumannGenerated]
  simp only [Set.star_empty, Set.union_empty, Set.centralizer_empty]
  rw [Algebra.eq_top_iff]
  simp [Semigroup.mem_center_iff, Subalgebra.mem_centralizer_iff, eq_comm]

theorem mem_finitePolarAlgebra_empty_iff_scalar
    (U B T : H →L[ℂ] H) :
    T ∈ finitePolarAlgebra U B ∅ ↔
      ∃ c : ℂ, T = c • (1 : H →L[ℂ] H) := by
  have he : {A : H →L[ℂ] H | ∃ n ∈ (∅ : Finset ℤ),
      A = polarConjugate U B n} = ∅ := by simp
  rw [finitePolarAlgebra, he, mem_vonNeumannGenerated_empty_iff_scalar]

end Invariant233

end OAI
