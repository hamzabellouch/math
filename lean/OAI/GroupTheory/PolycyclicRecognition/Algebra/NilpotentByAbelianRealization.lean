import OAI.GroupTheory.PolycyclicRecognition.Lattices.LatticeRealizationFiniteIndex
import OAI.GroupTheory.PolycyclicRecognition.Algebra.TorsionFreeAbelianRank
import OAI.GroupTheory.PolycyclicRecognition.Algebra.NilpotentByAbelianReduction

namespace OAI

/-! # Nonsplit nilpotent-by-abelian groups of polycyclic type -/

noncomputable section
namespace PolycyclicRecognition
open scoped IsMulCommutative
variable {G : Type} [Group G]

theorem nilpotent_by_abelian_uniform_lattice (hG : IsPolycyclic G)
    (ht : HasNoNontrivialTorsion G) (N : Subgroup G) [N.Normal]
    [Group.IsNilpotent N] [IsMulCommutative (G ⧸ N)] :
    ∃ K : Subgroup G, K.FiniteIndex ∧ ∃ (S : SimplyConnectedSolvableLieModel)
      (Λ : Subgroup S.carrier), IsUniformLattice Λ ∧ Nonempty (K ≃* Λ) := by
  let : Group.FG G := hG.finitelyGenerated
  let : CommGroup (G ⧸ N) := inferInstance
  have hQ : IsPolycyclic (G ⧸ N) := hG.of_surjective (QuotientGroup.mk' N)
    (QuotientGroup.mk'_surjective N)
  obtain ⟨U, hU, htf⟩ := hQ.exists_torsionFree_finiteIndex
  let := hU
  let : Group.FG U := inferInstance
  obtain ⟨n, ⟨e⟩⟩ := exists_integralLattice_equiv (A := U) htf
  let π := QuotientGroup.mk' N
  let H := U.comap π
  let : H.FiniteIndex := inferInstance
  let f : H →* U := (π.comp H.subtype).codRestrict U (fun x => x.property)
  have hf : Function.Surjective f := by
    intro u
    obtain ⟨g, hg⟩ := QuotientGroup.mk'_surjective N (u : G ⧸ N)
    have hgH : g ∈ H := by change π g ∈ U; rw [hg]; exact u.property
    exact ⟨⟨g, hgH⟩, Subtype.ext hg⟩
  let q := e.symm.toMonoidHom.comp f
  have hq : Function.Surjective q := e.symm.surjective.comp hf
  have hk (a : q.ker) : ((a : H) : G) ∈ N := by
    have ha : q (a : H) = 1 := a.property
    have hfa : f (a : H) = 1 := e.symm.injective
      (ha.trans (map_one e.symm.toMonoidHom).symm)
    have hh := congrArg (fun u : U => (u : G ⧸ N)) hfa
    exact (QuotientGroup.eq_one_iff _).mp hh
  let k : q.ker →* N := (H.subtype.comp q.ker.subtype).codRestrict N hk
  have hki : Function.Injective k := by
    intro a b hab
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun x : N => (x : G)) hab
  let : Group.IsNilpotent q.ker := nilpotent_of_injective_hom k hki
  have hi : Function.Injective (H.subtype.comp q.ker.subtype) :=
    Subtype.val_injective.comp Subtype.val_injective
  let : Group.FG q.ker := (hG.of_injective _ hi).finitelyGenerated
  have htk : HasNoNontrivialTorsion q.ker := ht.of_injective _ hi
  exact uniform_lattice_realization_of_finiteIndex H
    (nilpotent_integer_extension_realization q hq htk)

end PolycyclicRecognition

end

end OAI
