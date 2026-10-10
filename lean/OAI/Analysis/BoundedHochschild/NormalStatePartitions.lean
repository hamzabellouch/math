import OAI.Analysis.BoundedHochschild.CentralProjectionPartitions
import OAI.Analysis.BoundedHochschild.FiniteTraceCover

namespace OAI

/-! Central partitions into pieces with normal states faithful on their centers. -/

noncomputable section

open scoped ComplexOrder

namespace BoundedHochschild
namespace KadisonRingrose

universe u

variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

/-- Every von Neumann algebra has a central partition into pieces detected
faithfully on their centers by normal states. No traciality is asserted. -/
theorem exists_central_normal_state_partition (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) :
    ∃ D : MaximalCentralPartition M (HasCentralFaithfulNormalState e),
      D.complement = 0 := by
  obtain ⟨D⟩ := exists_maximal_central_partition e (HasCentralFaithfulNormalState e)
  refine ⟨D, ?_⟩
  by_contra hzero
  obtain ⟨p, hp, hpc, hple, hp0, hstate⟩ := exists_central_normal_state_subprojection e
    D.complement_isProjection D.complement_central hzero
  exact hp0 (D.maximal p hp hpc hple hstate)

end KadisonRingrose
end BoundedHochschild

end

end OAI
