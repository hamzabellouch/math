import OAI.GroupTheory.PolycyclicRecognition.Geometry.NilpotentFiniteRankRootCore
import OAI.GroupTheory.PolycyclicRecognition.Geometry.NilpotentRootDimension
import OAI.GroupTheory.PolycyclicRecognition.Algebra.AbelianNormalFiniteDimension

namespace OAI

/-! # The nilpotent-kernel finite-dimension endgame from rational H1

The rank premise is explicit. This module does not assert that FP-infinity
has already supplied it for arbitrary nilpotent kernels.
-/

noncomputable section
namespace PolycyclicRecognition
open CategoryTheory
open scoped IsMulCommutative

theorem nilpotent_finiteDimension_of_finite_abelianization
    {G : Type} [Group G] [Group.IsNilpotent G] [Countable G]
    (htf : HasNoNontrivialTorsion G)
    [Module.Finite ℚ (RationalAbelianSpace (Abelianization G))] :
    HasFiniteIntegralCohomologicalDimension G := by
  obtain ⟨H, hH, hroot⟩ := nilpotent_rootCore_of_finite_abelianization (G := G)
  exact nilpotent_finiteDimension_of_rootCore htf H hH hroot

theorem nilpotent_abelianization_virtual_finite_dimension
    {G : Type} [Group G] [Group.FG G]
    (N : Subgroup G) [N.Normal] [Group.IsNilpotent N] [IsMulCommutative (G ⧸ N)]
    (htfN : HasNoNontrivialTorsion N)
    [Module.Finite ℚ (RationalAbelianSpace (Abelianization N))] :
    ∃ V : Subgroup G, V.FiniteIndex ∧ Group.IsSolvable V ∧
      HasFiniteIntegralCohomologicalDimension V := by
  let : Group.IsSolvable G := Group.isSolvable_of_subgroup_quotient N
  let : Countable G := countable_of_group_fg G
  obtain ⟨d, hd⟩ := nilpotent_finiteDimension_of_finite_abelianization htfN
  let := hd
  have hQ : IsPolycyclic (G ⧸ N) := isPolycyclic_of_finitelyGenerated_nilpotent (G ⧸ N)
  obtain ⟨U, hU, htfU⟩ := hQ.exists_torsionFree_finiteIndex
  let := hU
  obtain ⟨r, ⟨e⟩⟩ := exists_integralLattice_equiv (A := U) htfU
  let π := QuotientGroup.mk' N
  let P := U.comap π
  let : P.FiniteIndex := inferInstance
  let f : P →* U := (π.comp P.subtype).codRestrict U (fun x => x.property)
  have hf : Function.Surjective f := by
    intro u
    obtain ⟨g, hg⟩ := QuotientGroup.mk'_surjective N (u : G ⧸ N)
    have hgP : g ∈ P := by change π g ∈ U; rw [hg]; exact u.property
    exact ⟨⟨g, hgP⟩, Subtype.ext hg⟩
  let q := e.symm.toMonoidHom.comp f
  have hq : Function.Surjective q := e.symm.surjective.comp hf
  have hk (a : q.ker) : ((a : P) : G) ∈ N := by
    have ha : q (a : P) = 1 := a.property
    have hfa : f (a : P) = 1 := e.symm.injective (ha.trans e.symm.map_one.symm)
    apply (QuotientGroup.eq_one_iff _).mp
    exact congrArg (fun u : U => (u : G ⧸ N)) hfa
  let k : q.ker →* N := (P.subtype.comp q.ker.subtype).codRestrict N hk
  have hki : Function.Injective k := by
    intro a b hab
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun x : N => (x : G)) hab
  let := cohomologicalDimension_le_of_injective k hki d
  let := cohomologicalDimension_le_of_lattice_quotient r q hq d
  exact ⟨P, inferInstance, inferInstance, d + r, inferInstance⟩

end PolycyclicRecognition

end

end OAI
