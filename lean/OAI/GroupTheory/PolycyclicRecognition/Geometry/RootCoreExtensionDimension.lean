import OAI.GroupTheory.PolycyclicRecognition.Geometry.NilpotentRootDimension
import OAI.GroupTheory.PolycyclicRecognition.Algebra.AbelianQuotientDimension

namespace OAI

/-! # The finite-dimensional nilpotent-by-abelian step

Only an actual finite root core in the nilpotent kernel and a finite-rank
torsion-free abelian quotient are used. No cohomological dimension premise
for the kernel or ambient group is needed.
-/

noncomputable section
namespace PolycyclicRecognition
open CategoryTheory
open scoped IsMulCommutative

theorem finiteDimension_of_nilpotent_rootCore_abelian_quotient
    {G : Type} [Group G] [Countable G] (N : Subgroup G) [N.Normal]
    [Group.IsNilpotent N] [IsMulCommutative (G ⧸ N)]
    (htf : HasNoNontrivialTorsion N)
    (H : Subgroup N) (hH : H.FG)
    (hroot : ∀ g : N, ∃ n : ℕ, 0 < n ∧ g ^ n ∈ H)
    (htfQ : HasNoNontrivialTorsion (G ⧸ N))
    (r : ℕ) (hrank : Module.rank ℤ (Additive (G ⧸ N)) ≤ r) :
    HasFiniteIntegralCohomologicalDimension G := by
  obtain ⟨d, hd⟩ := nilpotent_finiteDimension_of_rootCore htf H hH hroot
  let := hd
  exact ⟨d + r + 1, cohomologicalDimension_le_of_abelian_quotient N d r htfQ hrank⟩

end PolycyclicRecognition

end

end OAI
