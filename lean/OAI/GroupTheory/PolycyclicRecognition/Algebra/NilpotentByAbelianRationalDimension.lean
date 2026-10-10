import OAI.GroupTheory.PolycyclicRecognition.Algebra.RationalExtensionDimension
import OAI.GroupTheory.PolycyclicRecognition.Finiteness.LocallyFiniteCoefficientHomology
import OAI.GroupTheory.PolycyclicRecognition.Algebra.NilpotentTorsionQuotientEndgame

namespace OAI

/-! # Rational dimension of finitely generated nilpotent-by-abelian groups

Finite rational kernel abelianization is equivalent to a uniform rational
homology bound for the ambient group. The implication from FP-infinity is
not assumed or supplied by this equivalence.
-/
noncomputable section
namespace PolycyclicRecognition
open scoped IsMulCommutative
variable {G : Type} [Group G] [Group.FG G]
variable (N : Subgroup G) [N.Normal] [Group.IsNilpotent N]
variable [IsMulCommutative (G ⧸ N)]

theorem nilpotentByAbelian_rational_dimension_iff_kernel_rank :
    (∃ d : ℕ, RationalHomologyDimensionLE G d) ↔
      Module.Finite ℚ (RationalAbelianSpace (Abelianization N)) := by
  constructor
  · rintro ⟨d, hd⟩
    exact nilpotent_rational_abelianization_finite_of_homology_bound (hd.subgroup N)
  · intro h
    let := h
    let : Countable G := countable_of_group_fg G
    obtain ⟨a, ha⟩ := nilpotent_rational_homology_bounded_of_abelianization (G := N)
    obtain ⟨b, hb⟩ := finitelyGenerated_nilpotent_rational_homology_bounded (G := G ⧸ N)
    exact ⟨a + b, rational_homology_bound_of_extension N ha hb⟩

theorem nilpotentByAbelian_mod_torsion_finite_dimension_of_rational_bound
    {d : ℕ} (hd : RationalHomologyDimensionLE G d) :
    ∃ V : Subgroup (G ⧸ normalNilpotentTorsionSubgroup N),
      V.FiniteIndex ∧ Group.IsSolvable V ∧ HasFiniteIntegralCohomologicalDimension V := by
  let := nilpotent_rational_abelianization_finite_of_homology_bound (hd.subgroup N)
  exact nilpotent_abelianization_mod_torsion_virtual_finite_dimension N

end PolycyclicRecognition

end

end OAI
