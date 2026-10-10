import OAI.GroupTheory.PolycyclicRecognition.Algebra.ClassTwoScalarBracket
import OAI.GroupTheory.PolycyclicRecognition.Geometry.AbelianFiniteRankRootCore
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CentralExtensionRootCore
import OAI.GroupTheory.PolycyclicRecognition.Geometry.NilpotentRootDimension

namespace OAI

/-! # Class-two groups of finite rational abelianization rank

The central exterior bracket bounds the derived layer. Finite root cores in
that layer and the abelianization then lift to an actual root core in the
group. Torsion-free countable groups consequently have finite integral
cohomological dimension.
-/

noncomputable section
namespace PolycyclicRecognition
open scoped IsMulCommutative
variable {G : Type} [Group G]

theorem classTwo_rootCore_of_finite_abelianization
    (h : commutator G ≤ Subgroup.center G)
    [Module.Finite ℚ (RationalAbelianSpace (Abelianization G))] :
    ∃ H : Subgroup G, H.FG ∧ ∀ g, ∃ n : ℕ, 0 < n ∧ g ^ n ∈ H := by
  let : IsMulCommutative (commutator G) := ⟨⟨fun a b =>
    Subtype.ext (Subgroup.mem_center_iff.mp (h a.property) b).symm⟩⟩
  let : Module.Finite ℚ (RationalAbelianSpace (commutator G)) :=
    classTwo_scalar_derived_finite ℚ h
  apply central_extension_rootCore (commutator G) h
  · exact abelian_finiteRank_rootCore
  · exact abelian_finiteRank_rootCore (A := Abelianization G)

theorem classTwo_finiteDimension_of_finite_abelianization [Countable G]
    (h : commutator G ≤ Subgroup.center G) (htf : HasNoNontrivialTorsion G)
    [Module.Finite ℚ (RationalAbelianSpace (Abelianization G))] :
    HasFiniteIntegralCohomologicalDimension G := by
  let : IsMulCommutative (G ⧸ Subgroup.center G) :=
    Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr h
  let : Group.IsNilpotent G :=
    Subgroup.isNilpotent_of_ker_le_center (QuotientGroup.mk' (Subgroup.center G)) (by
      rw [QuotientGroup.ker_mk'])
  obtain ⟨H, hH, hroot⟩ := classTwo_rootCore_of_finite_abelianization h
  exact nilpotent_finiteDimension_of_rootCore htf H hH hroot

end PolycyclicRecognition

end

end OAI
