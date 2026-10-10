import OAI.GroupTheory.PolycyclicRecognition.Finiteness.FiniteResolutionTruncation
import OAI.GroupTheory.PolycyclicRecognition.Finiteness.NormalInductionDimension

namespace OAI

/-! # Infinite cyclic extensions of groups of finite integral dimension

Finite generation of the kernel's projective resolution is unnecessary for
the dimension bound. Truncate an arbitrary resolution before induction.
-/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory
variable {G : Type} [Group G]

theorem cohomologicalDimension_le_of_infiniteCyclicQuotient
    (N : Subgroup G) [N.Normal] [IsCyclic (G ⧸ N)] [Infinite (G ⧸ N)]
    (d : ℕ) [HasProjectiveDimensionLE (trivialIntegral N) d] :
    HasProjectiveDimensionLE (trivialIntegral G) (d + 1) := by
  let : CommGroup (G ⧸ N) := IsCyclic.commGroup
  obtain ⟨z, hz⟩ := IsCyclic.exists_generator (α := G ⧸ N)
  let P := Rep.standardResolution ℤ N
  let R := finiteProjectiveResolution P d
  let := quotientRegular_projectiveDimension N R d (finiteTruncation_isZero P d)
  exact cohomologicalDimension_bound_of_cyclicQuotientModule
    (G ⧸ N) (QuotientGroup.mk' N) z hz d

theorem finiteCohomologicalDimension_of_infiniteCyclicQuotient
    (N : Subgroup G) [N.Normal] [IsCyclic (G ⧸ N)] [Infinite (G ⧸ N)]
    (hN : HasFiniteIntegralCohomologicalDimension N) :
    HasFiniteIntegralCohomologicalDimension G := by
  obtain ⟨d, hd⟩ := hN
  let := hd
  exact ⟨d + 1, cohomologicalDimension_le_of_infiniteCyclicQuotient N d⟩

end PolycyclicRecognition

end

end OAI
