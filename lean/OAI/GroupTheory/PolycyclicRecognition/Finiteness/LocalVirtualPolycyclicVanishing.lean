import OAI.GroupTheory.PolycyclicRecognition.Algebra.SmallCoefficientFiniteIndex
import OAI.GroupTheory.PolycyclicRecognition.Finiteness.LocalInductionVanishing
import OAI.GroupTheory.PolycyclicRecognition.Finiteness.PolyZDuality
import OAI.GroupTheory.PolycyclicRecognition.Algebra.Nilpotent

namespace OAI

/-! # Vanishing for locally virtually polycyclic height kernels

The finite-index passage uses the constructed relative trace, allowing torsion
and avoiding a uniform bound on the ranks of finitely generated subgroups.
-/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory
attribute [local instance 2000] Rep.hV2 Rep.instLinear
variable {G : Type} [Group G]

theorem IsVirtuallyPolycyclic.exists_poincareDuality_finiteIndex
    (hG : IsVirtuallyPolycyclic G) :
    ∃ V : Subgroup G, V.FiniteIndex ∧ ∃ n, IsIntegralPoincareDualityGroup V n := by
  obtain ⟨N, hi, hN⟩ := hG
  obtain ⟨T, ht, n, hT⟩ := hN.exists_poincareDuality_finiteIndex
  let V := T.map N.subtype
  have hV : V.FiniteIndex := ⟨by
    change (T.map N.subtype).index ≠ 0
    rw [Subgroup.index_map_subtype]
    exact mul_ne_zero ht.index_ne_zero hi.index_ne_zero⟩
  let e : T ≃* V := T.equivMapOfInjective N.subtype N.subtype_injective
  exact ⟨V, hV, n, hT.of_equiv e⟩

theorem smallCoefficient_virtuallyPolycyclic_finite_dimension [Countable G]
    (J : Subgroup G) (hfg : J.FG) (hJ : IsVirtuallyPolycyclic J) :
    ∃ d : ℕ, HasProjectiveDimensionLE (Rep.res J.subtype (smallCoefficientRepresentation G)) d := by
  let : Group.FG J := (Group.fg_iff_subgroup_fg J).mpr hfg
  obtain ⟨N, hi, n, hN⟩ := hJ.exists_poincareDuality_finiteIndex
  let := hi
  have hNfg : N.FG := (Group.fg_iff_subgroup_fg N).mp inferInstance
  obtain ⟨d, hd⟩ := hN.finiteCohomologicalDimension N
  exact ⟨d, smallCoefficient_finiteIndex_dimension_le G J hfg N hNfg d hd⟩

theorem TypeFPInfinity.locallyVirtuallyPolycyclic_smallCoefficient_induction_vanishing
    [Countable G] (hG : TypeFPInfinity G) (K : Subgroup G) (p : ℕ)
    (hlocal : ∀ J : Subgroup G, J ≤ K → J.FG → IsVirtuallyPolycyclic J) :
    Subsingleton (ShiftedCompletedCohomology p
      (Rep.ind K.subtype (Rep.res K.subtype (smallCoefficientRepresentation G)))) := by
  apply hG.induction_locally_finite_dimension_vanishing (smallCoefficientRepresentation G) K p
  intro J hJK hfg
  exact smallCoefficient_virtuallyPolycyclic_finite_dimension J hfg (hlocal J hJK hfg)

theorem TypeFPInfinity.locallyVirtuallyNilpotent_smallCoefficient_induction_vanishing
    [Countable G] (hG : TypeFPInfinity G) (K : Subgroup G) (p : ℕ)
    (hlocal : ∀ J : Subgroup G, J ≤ K → J.FG → Group.IsVirtuallyNilpotent J) :
    Subsingleton (ShiftedCompletedCohomology p
      (Rep.ind K.subtype (Rep.res K.subtype (smallCoefficientRepresentation G)))) := by
  apply hG.locallyVirtuallyPolycyclic_smallCoefficient_induction_vanishing K p
  intro J hJK hfg
  let : Group.FG J := (Group.fg_iff_subgroup_fg J).mpr hfg
  exact isVirtuallyPolycyclic_of_finitelyGenerated_virtuallyNilpotent J (hlocal J hJK hfg)

end PolycyclicRecognition

end

end OAI
