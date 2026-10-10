import OAI.GroupTheory.PolycyclicRecognition.Finiteness.RationalCoefficientDimensionBound
import OAI.GroupTheory.PolycyclicRecognition.Algebra.LocallyNilpotentDimension
import OAI.GroupTheory.PolycyclicRecognition.Algebra.NilpotentGeneratorRank
import OAI.GroupTheory.PolycyclicRecognition.Algebra.CountableUnionDimension

namespace OAI

/-! # Integral dimension from a rational bound for locally nilpotent groups

A finitely generated torsion-free nilpotent subgroup is an integral duality
group. Its orientation class detects its dimension over the rationals.
The countable exhaustion therefore has uniformly bounded integral dimension.
-/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory
variable {G : Type} [Group G]

theorem RationalHomologyDimensionLE.nilpotent_subgroup_dimension {d : ℕ}
    (hd : RationalHomologyDimensionLE G d) (H : Subgroup G) (hH : H.FG)
    [Group.IsNilpotent H] (htf : HasNoNontrivialTorsion H) :
    HasProjectiveDimensionLE (trivialIntegral H) d := by
  let : Group.FG H := (Group.fg_iff_subgroup_fg H).mpr hH
  obtain ⟨n, hn⟩ := nilpotent_poincareDuality_of_finitelyGenerated_torsionFree htf
  let := hn.cohomologicalDimension
  exact hasProjectiveDimensionLT_of_ge (trivialIntegral H) (n + 1) (d + 1)
    (Nat.add_le_add_right (hn.dimension_le_of_rational_homology_bound (hd.subgroup H)) 1)

theorem RationalHomologyDimensionLE.nilpotent_subgroup_rank {d : ℕ}
    (hd : RationalHomologyDimensionLE G d) (H : Subgroup G) [Group.FG H]
    [Group.IsNilpotent H] (htf : HasNoNontrivialTorsion H) : Group.rank H ≤ d := by
  obtain ⟨n, hn, hr⟩ :=
    (nilpotent_polyZ_of_finitelyGenerated_torsionFree htf).exists_poincareDuality_rank_bound
  exact hr.trans (hn.dimension_le_of_rational_homology_bound (hd.subgroup H))

theorem RationalHomologyDimensionLE.locallyNilpotent_integralDimension [Countable G]
    {d : ℕ} (hd : RationalHomologyDimensionLE G d)
    (htf : HasNoNontrivialTorsion G)
    (hlocal : ∀ H : Subgroup G, H.FG → Group.IsNilpotent H) :
    HasProjectiveDimensionLE (trivialIntegral G) (d + 1) := by
  apply cohomologicalDimension_le_of_fg_subgroups d
  intro H hH
  let := hlocal H hH
  exact hd.nilpotent_subgroup_dimension H hH
    (htf.of_injective H.subtype Subtype.val_injective)

theorem RationalHomologyDimensionLE.locallyNilpotent_isNilpotent [Countable G]
    {d : ℕ} (hd : RationalHomologyDimensionLE G d)
    (htf : HasNoNontrivialTorsion G)
    (hlocal : ∀ H : Subgroup G, H.FG → Group.IsNilpotent H) :
    Group.IsNilpotent G := by
  apply (show HasFiniteIntegralCohomologicalDimension G from
    ⟨d + 1, hd.locallyNilpotent_integralDimension htf hlocal⟩).nilpotent_of_locallyNilpotent
  intro H hH
  exact hlocal H ((Group.fg_iff_subgroup_fg H).mp hH)

end PolycyclicRecognition

end

end OAI
