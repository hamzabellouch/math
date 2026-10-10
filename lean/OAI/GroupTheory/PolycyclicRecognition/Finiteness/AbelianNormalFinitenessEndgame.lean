import OAI.GroupTheory.PolycyclicRecognition.Algebra.AbelianNormalTorsion
import OAI.GroupTheory.PolycyclicRecognition.Algebra.AbelianNormalFiniteDimension
import OAI.GroupTheory.PolycyclicRecognition.Algebra.FiniteIndexKernelQuotient
import OAI.GroupTheory.PolycyclicRecognition.Algebra.FiniteKernelAbelianQuotient

namespace OAI

/-! # The FP-infinity finiteness endgame for abelian-by-abelian groups

No finite generation, rank, or torsion-free hypothesis is imposed on the
abelian kernel. These are the actual finite projective resolution consequences.
-/

noncomputable section
namespace PolycyclicRecognition
open CategoryTheory
open scoped IsMulCommutative
variable {G : Type} [Group G] [Group.FG G]
  (N : Subgroup G) [N.Normal] [IsMulCommutative N] [IsMulCommutative (G ⧸ N)]

include N in
theorem abelian_normal_virtual_finite_dimension (h : TypeFPInfinity G) :
    ∃ V : Subgroup G, V.FiniteIndex ∧ Group.IsSolvable V ∧
      HasFiniteIntegralCohomologicalDimension V := by
  let : Group.IsSolvable G := Group.isSolvable_of_subgroup_quotient N
  let : Countable G := countable_of_group_fg G
  obtain ⟨K, hKchar, hKindex, hKtf⟩ :=
    abelian_normal_kernel_characteristic_finiteIndex_torsionFree N h
  let := hKchar
  let := hKindex
  obtain ⟨d, hd⟩ := abelian_normal_kernel_finite_rank N h
  have hKr : Module.rank ℤ (Additive K) ≤ d :=
    ((K.subtype.toAdditive.toIntLinearMap).rank_le_of_injective K.subtype_injective).trans hd
  let : HasProjectiveDimensionLE (trivialIntegral K) (d + 1) :=
    abelian_cohomologicalDimension_of_rank d hKr hKtf
  let A := K.map N.subtype
  let eA := K.equivMapOfInjective N.subtype N.subtype_injective
  let : HasProjectiveDimensionLE (trivialIntegral A) (d + 1) :=
    cohomologicalDimension_le_of_equiv eA (d + 1)
  let f := finiteIndexKernelQuotientMap N K
  let : Finite f.ker := finiteIndexKernelQuotientMap_kernel_finite N K
  obtain ⟨U, hU, r, ⟨e⟩⟩ :=
    finite_kernel_abelian_quotient_lattice f (finiteIndexKernelQuotientMap_surjective N K)
  let := hU
  let π := QuotientGroup.mk' A
  let P := U.comap π
  let : P.FiniteIndex := inferInstance
  let g : P →* U := (π.comp P.subtype).codRestrict U (fun x => x.property)
  have hg : Function.Surjective g := by
    intro u
    obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective A (u : G ⧸ A)
    have hxP : x ∈ P := by change π x ∈ U; rw [hx]; exact u.property
    exact ⟨⟨x, hxP⟩, Subtype.ext hx⟩
  let q := e.symm.toMonoidHom.comp g
  have hq : Function.Surjective q := e.symm.surjective.comp hg
  have hk (a : q.ker) : ((a : P) : G) ∈ A := by
    apply (QuotientGroup.eq_one_iff _).mp
    have ha : q (a : P) = 1 := a.property
    have hga : g (a : P) = 1 := e.symm.injective (ha.trans e.symm.map_one.symm)
    exact congrArg (fun u : U => (u : G ⧸ A)) hga
  let k : q.ker →* A := (P.subtype.comp q.ker.subtype).codRestrict A hk
  have hki : Function.Injective k := by
    intro a b hab
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun x : A => (x : G)) hab
  let := cohomologicalDimension_le_of_injective k hki (d + 1)
  let := cohomologicalDimension_le_of_lattice_quotient r q hq (d + 1)
  exact ⟨P, inferInstance, inferInstance, d + 1 + r, inferInstance⟩

end PolycyclicRecognition

end

end OAI
