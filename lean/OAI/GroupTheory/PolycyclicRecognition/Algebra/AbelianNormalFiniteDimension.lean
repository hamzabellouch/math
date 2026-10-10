import OAI.GroupTheory.PolycyclicRecognition.Algebra.AbelianNormalFiniteRank
import OAI.GroupTheory.PolycyclicRecognition.Algebra.AbelianRankDimension
import OAI.GroupTheory.PolycyclicRecognition.Lattices.LatticeQuotientDimension
import OAI.GroupTheory.PolycyclicRecognition.Algebra.PolycyclicTorsionFree
import OAI.GroupTheory.PolycyclicRecognition.Algebra.FinitelyGeneratedCountable

namespace OAI

/-! # The finite-dimensional endgame for a torsion-free abelian kernel

The quotient may be any finitely generated abelian group. Passing to a finite
index subgroup removes its torsion, and the actual rational rank bounds the
kernel's integral cohomological dimension.
-/

noncomputable section
namespace PolycyclicRecognition
open scoped IsMulCommutative
variable {G : Type} [Group G] [Group.FG G]
  (N : Subgroup G) [N.Normal] [IsMulCommutative N] [IsMulCommutative (G ⧸ N)]

theorem abelian_normal_torsionFree_virtual_finite_dimension (h : TypeFPInfinity G)
    (htfN : HasNoNontrivialTorsion N) :
    ∃ V : Subgroup G, V.FiniteIndex ∧ Group.IsSolvable V ∧
      HasFiniteIntegralCohomologicalDimension V := by
  let : Group.IsSolvable G := Group.isSolvable_of_subgroup_quotient N
  let : Countable G := countable_of_group_fg G
  obtain ⟨d, hd⟩ := abelian_normal_kernel_finite_rank N h
  let := abelian_cohomologicalDimension_of_rank d hd htfN
  have hQ : IsPolycyclic (G ⧸ N) := isPolycyclic_of_finitelyGenerated_nilpotent (G ⧸ N)
  obtain ⟨U, hU, htfU⟩ := hQ.exists_torsionFree_finiteIndex
  let := hU
  let : Group.FG U := inferInstance
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
  let := cohomologicalDimension_le_of_injective k hki (d + 1)
  let := cohomologicalDimension_le_of_lattice_quotient r q hq (d + 1)
  exact ⟨P, inferInstance, inferInstance, d + 1 + r, inferInstance⟩

end PolycyclicRecognition

end

end OAI
