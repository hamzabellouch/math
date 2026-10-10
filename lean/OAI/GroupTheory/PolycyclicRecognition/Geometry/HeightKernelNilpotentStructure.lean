import OAI.GroupTheory.PolycyclicRecognition.Algebra.LocallyNilpotentRationalEndgame
import OAI.GroupTheory.PolycyclicRecognition.Algebra.RationalNilpotentRank
import OAI.GroupTheory.PolycyclicRecognition.Algebra.NilpotentTorsionQuotientEndgame

namespace OAI

/-! # Locally nilpotent height kernels

The coefficient dimension and finite-subgroup order bound imply torsion
freeness and finite rank of the kernel.
-/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory ThompsonNonamenability
open scoped IsMulCommutative
variable {G : Type} [Group G] [Group.FG G]

theorem TypeFPInfinity.heightKernel_locallyNilpotent_nilpotent
    (hG : TypeFPInfinity G) (M : InvariantMean G) (N : Subgroup G) [N.Normal]
    (hQ : HasFiniteIntegralCohomologicalDimension (G ⧸ N))
    (hN : ∀ J : Subgroup G, J ≤ N → J.FG → Group.IsNilpotent J) :
    Group.IsNilpotent N := by
  let : Countable G := countable_of_group_fg G
  have hNv : ∀ J : Subgroup G, J ≤ N → J.FG → Group.IsVirtuallyNilpotent J :=
    fun J hJN hJ => (hN J hJN hJ).isVirtuallyNilpotent
  obtain ⟨d, hd⟩ := hG.heightKernel_rationalCoefficient_finite_dimension M N hQ hNv
  have hR := rationalGroup_dimension_le_of_integral_rational d hd
  have hb := hG.heightKernel_boundedFiniteSubgroupOrders M N hQ hNv
  apply rationallyFinite_locallyNilpotent_isNilpotent d
    (RationalQuotient.rational_dimension_subgroup N d hR) (hb.subgroup N)
  intro J hJ
  let := hN (J.map N.subtype) (by
    rintro _ ⟨x, _, rfl⟩
    exact x.property) (fg_subgroup_map hJ N.subtype)
  exact Group.nilpotent_of_mulEquiv (J.equivMapOfInjective N.subtype Subtype.val_injective).symm

theorem TypeFPInfinity.heightKernel_locallyNilpotent_structure
    (hG : TypeFPInfinity G) (M : InvariantMean G) (N : Subgroup G) [N.Normal]
    [IsMulCommutative (G ⧸ N)]
    (hQ : HasFiniteIntegralCohomologicalDimension (G ⧸ N))
    (hN : ∀ J : Subgroup G, J ≤ N → J.FG → Group.IsNilpotent J) :
    ∃ T : Subgroup G, ∃ hT : T.Normal, letI := hT
      Finite T ∧ (∃ V : Subgroup (G ⧸ T), V.FiniteIndex ∧ Group.IsSolvable V ∧
        HasFiniteIntegralCohomologicalDimension V) := by
  let : Countable G := countable_of_group_fg G
  let := hG.heightKernel_locallyNilpotent_nilpotent M N hQ hN
  have hNv : ∀ J : Subgroup G, J ≤ N → J.FG → Group.IsVirtuallyNilpotent J :=
    fun J hJN hJ => (hN J hJN hJ).isVirtuallyNilpotent
  obtain ⟨d, hd⟩ := hG.heightKernel_rationalHomologyDimension M N hQ hNv
  let := nilpotent_rational_abelianization_finite_of_homology_bound (hd.subgroup N)
  have hb := hG.heightKernel_boundedFiniteSubgroupOrders M N hQ hNv
  let T := nilpotentTorsionSubgroup (G := N)
  let : Finite T := finite_locallyFinite_normal_subgroup T
    nilpotentTorsionSubgroup_locallyFinite (hb.subgroup N)
  let e := T.equivMapOfInjective N.subtype Subtype.val_injective
  let : Finite (normalNilpotentTorsionSubgroup N) := Finite.of_equiv T e.toEquiv
  exact ⟨normalNilpotentTorsionSubgroup N, inferInstance, inferInstance,
    nilpotent_abelianization_mod_torsion_virtual_finite_dimension N⟩

theorem TypeFPInfinity.heightKernel_locallyNilpotent_virtualSolvable
    (hG : TypeFPInfinity G) (M : InvariantMean G) (N : Subgroup G) [N.Normal]
    [IsMulCommutative (G ⧸ N)]
    (hQ : HasFiniteIntegralCohomologicalDimension (G ⧸ N))
    (hN : ∀ J : Subgroup G, J ≤ N → J.FG → Group.IsNilpotent J) :
    ∃ H : Subgroup G, H.FiniteIndex ∧ Group.IsSolvable H := by
  obtain ⟨T, hT, hTf, V, hV, hVs, _⟩ :=
    hG.heightKernel_locallyNilpotent_structure M N hQ hN
  let := hT
  let : Finite (QuotientGroup.mk' T).ker := by simpa only [QuotientGroup.ker_mk'] using hTf
  exact virtually_solvable_of_finite_kernel_virtual_quotient (QuotientGroup.mk' T)
    ⟨V, hV, hVs⟩

end PolycyclicRecognition

end

end OAI
