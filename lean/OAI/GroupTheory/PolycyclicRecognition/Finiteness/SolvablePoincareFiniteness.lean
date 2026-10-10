import OAI.GroupTheory.PolycyclicRecognition.Finiteness.NilpotentLatticeFiniteness
import OAI.GroupTheory.PolycyclicRecognition.Algebra.NilpotentByAbelianReduction
import OAI.GroupTheory.PolycyclicRecognition.Algebra.FinitelyGeneratedCountable
import OAI.GroupTheory.PolycyclicRecognition.Algebra.PolycyclicTorsionFree
import OAI.GroupTheory.PolycyclicRecognition.Algebra.TorsionFreeAbelianRank
import OAI.GroupTheory.PolycyclicRecognition.Algebra.SolvableFiniteExtension
import OAI.GroupTheory.PolycyclicRecognition.Finiteness.FiniteIndexFiniteness

namespace OAI

/-! # The solvable integral Poincare duality finiteness theorem -/

noncomputable section
namespace PolycyclicRecognition
open scoped IsMulCommutative
variable {G : Type} [Group G] [Group.IsSolvable G]

theorem polycyclic_of_nilpotent_by_abelian_duality (N : Subgroup G) [N.Normal]
    [Group.IsNilpotent N] [IsMulCommutative (G ⧸ N)] {n : ℕ}
    (hG : IsIntegralPoincareDualityGroup G n) : IsPolycyclic G := by
  let : Group.FG G := hG.1.fg
  let : CommGroup (G ⧸ N) := inferInstance
  have hQ : IsPolycyclic (G ⧸ N) := isPolycyclic_of_finitelyGenerated_nilpotent (G ⧸ N)
  obtain ⟨U, hU, htf⟩ := hQ.exists_torsionFree_finiteIndex
  let := hU
  let : Group.FG U := inferInstance
  obtain ⟨r, ⟨e⟩⟩ := exists_integralLattice_equiv (A := U) htf
  let π := QuotientGroup.mk' N
  let P := U.comap π
  let : P.FiniteIndex := inferInstance
  let f : P →* U := (π.comp P.subtype).codRestrict U (fun x => x.property)
  have hf : Function.Surjective f := by
    intro u
    obtain ⟨g, hg⟩ := QuotientGroup.mk'_surjective N (u : G ⧸ N)
    have hgP : g ∈ P := by change π g ∈ U; rw [hg]; exact u.property
    refine ⟨⟨g, hgP⟩, ?_⟩
    apply Subtype.ext
    exact hg
  let q := e.symm.toMonoidHom.comp f
  have hq : Function.Surjective q := e.symm.surjective.comp hf
  have hk (a : q.ker) : ((a : P) : G) ∈ N := by
    have ha : q (a : P) = 1 := a.property
    have hfa : f (a : P) = 1 := by
      apply e.symm.injective
      exact ha.trans (map_one e.symm.toMonoidHom).symm
    have hh := congrArg (fun u : U => (u : G ⧸ N)) hfa
    change π ((a : P) : G) = ((1 : U) : G ⧸ N) at hh
    have hπ : π ((a : P) : G) = 1 := by
      simpa only [Subgroup.coe_one] using hh
    exact (QuotientGroup.eq_one_iff _).mp hπ
  let k : q.ker →* N := (P.subtype.comp q.ker.subtype).codRestrict N hk
  have hki : Function.Injective k := by
    intro a b hab
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun x : N => (x : G)) hab
  let : Group.IsNilpotent q.ker := nilpotent_of_injective_hom k hki
  let : Group.FG P := inferInstance
  let : Countable P := countable_of_group_fg P
  have hP : IsPolycyclic P := polycyclic_of_nilpotent_latticeQuotient r q hq
    (hG.finiteIndex_subgroup P)
  exact (show IsVirtuallyPolycyclic G from ⟨P, inferInstance, hP⟩).polycyclic_of_solvable

theorem IsIntegralPoincareDualityGroup.polycyclic {n : ℕ}
    (hG : IsIntegralPoincareDualityGroup G n) : IsPolycyclic G := by
  obtain ⟨H, hHn, hHi, N, hNn, hNnil, hQ⟩ :=
    exists_finiteIndex_nilpotent_by_abelian (hG.finiteCohomologicalDimension G)
  let := hHn
  let := hHi
  let := hNn
  let := hNnil
  let := hQ
  have hH := polycyclic_of_nilpotent_by_abelian_duality N (hG.finiteIndex_subgroup H)
  exact (show IsVirtuallyPolycyclic G from ⟨H, hHi, hH⟩).polycyclic_of_solvable

theorem bieriDualityInput : BieriDualityInput := by
  intro H _ _ n hH
  exact hH.polycyclic

end PolycyclicRecognition

end

end OAI
