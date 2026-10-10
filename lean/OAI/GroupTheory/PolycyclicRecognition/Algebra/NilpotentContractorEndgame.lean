import OAI.GroupTheory.PolycyclicRecognition.Geometry.CyclicJoinHeight
import OAI.GroupTheory.PolycyclicRecognition.Algebra.NilpotentAscendingBase
import OAI.GroupTheory.PolycyclicRecognition.Finiteness.AscendingFinitenessEndgame
import OAI.GroupTheory.PolycyclicRecognition.Algebra.FiniteOrderAscendingBase

namespace OAI

/-! # The endgame from a contracting element in a nilpotent normal subgroup

The contracting condition is stated on the actual abelianization and is
lifted by the proved nilpotent ascending-base theorem. Centrality modulo the
nilpotent subgroup makes the generated cyclic extension normal.
-/

noncomputable section
namespace PolycyclicRecognition
variable {G : Type} [Group G]

theorem IsVirtuallyPolycyclic.of_surjective {Q : Type} [Group Q]
    (hG : IsVirtuallyPolycyclic G) (q : G →* Q) (hq : Function.Surjective q) :
    IsVirtuallyPolycyclic Q := by
  obtain ⟨H, hHindex, hHpoly⟩ := hG
  let := hHindex
  exact ⟨H.map q, Subgroup.FiniteIndex.map_of_surjective H hq,
    hHpoly.of_surjective (q.subgroupMap H) (q.subgroupMap_surjective H)⟩

theorem cyclicJoin_eq_comap_zpowers (N : Subgroup G) [N.Normal] (t : G) :
    cyclicJoin N t = (Subgroup.zpowers ((QuotientGroup.mk' N) t)).comap (QuotientGroup.mk' N) := by
  rw [← MonoidHom.map_zpowers, QuotientGroup.comap_map_mk']

theorem cyclicJoin_normal_of_central_quotient (N : Subgroup G) [N.Normal] (t : G)
    (ht : (QuotientGroup.mk' N) t ∈ Subgroup.center (G ⧸ N)) :
    (cyclicJoin N t).Normal := by
  let : (Subgroup.zpowers ((QuotientGroup.mk' N) t)).Normal :=
    (Subgroup.zpowers _).normal_of_le_center (Subgroup.zpowers_le.mpr ht)
  rw [cyclicJoin_eq_comap_zpowers]
  infer_instance

def ascendingData_cyclicJoin (N : Subgroup G) [N.Normal] [Group.IsNilpotent N] (t : G)
    [Infinite (Subgroup.zpowers ((QuotientGroup.mk' N) t))]
    (hbase : HasFinitelyGeneratedAscendingBase (MulAut.conjNormal (H := N) t)) :
    AscendingVirtuallyNilpotentData (cyclicJoin N t) := by
  let h := cyclicJoinHeight N t
  let u := cyclicJoinLetter N t
  let e := cyclicJoinHeightKernelEquiv N t
  let : Group.IsNilpotent h.ker := Group.nilpotent_of_mulEquiv e.symm
  have hk := hbase.of_equiv e (MulAut.conjNormal (H := h.ker) u)
    (MulAut.conjNormal (H := N) t) (cyclicJoinHeightKernelEquiv_conj N t)
  let B := hk.choose
  exact
    { height := h
      letter := u
      height_letter := cyclicJoinHeight_letter N t
      base := B
      base_fg := (Group.fg_iff_subgroup_fg B).mpr hk.choose_spec.1
      base_nilpotent := Group.IsNilpotent.isVirtuallyNilpotent inferInstance
      stable := hk.choose_spec.2.1
      exhaustive := hk.choose_spec.2.2 }

theorem virtualSolvableFiniteDimension_of_nilpotent_contractor
    (N : Subgroup G) [N.Normal] [Group.IsNilpotent N] (t : G)
    [Infinite (Subgroup.zpowers ((QuotientGroup.mk' N) t))]
    (ht : (QuotientGroup.mk' N) t ∈ Subgroup.center (G ⧸ N))
    (hbase : HasFinitelyGeneratedAscendingBase
      (characteristicQuotientAut (commutator N) (MulAut.conjNormal (H := N) t)))
    (hQ : IsVirtuallyPolycyclic (G ⧸ N)) :
    ∃ V : Subgroup G, V.FiniteIndex ∧ Group.IsSolvable V ∧
      HasFiniteIntegralCohomologicalDimension V := by
  let K := cyclicJoin N t
  let : K.Normal := cyclicJoin_normal_of_central_quotient N t ht
  let D := ascendingData_cyclicJoin N t
    (nilpotent_ascending_base_of_abelianization (MulAut.conjNormal (H := N) t) hbase)
  let q : G ⧸ N →* G ⧸ K := QuotientGroup.map N K (MonoidHom.id G)
    (show N ≤ K from le_sup_left)
  have hq : Function.Surjective q := by
    intro x
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective K x
    exact ⟨(QuotientGroup.mk' N) g, rfl⟩
  exact virtualSolvableFiniteDimension_of_ascending_normal_subgroup K D (hQ.of_surjective q hq)


theorem virtualSolvableFiniteDimension_of_nilpotent_abelian_contractor
    (N : Subgroup G) [N.Normal] [Group.IsNilpotent N] (t : G)
    (ht : (QuotientGroup.mk' N) t ∈ Subgroup.center (G ⧸ N))
    (hbase : HasFinitelyGeneratedAscendingBase
      (characteristicQuotientAut (commutator N) (MulAut.conjNormal (H := N) t)))
    (hQ : IsVirtuallyPolycyclic (G ⧸ N)) :
    ∃ V : Subgroup G, V.FiniteIndex ∧ Group.IsSolvable V ∧
      HasFiniteIntegralCohomologicalDimension V := by
  cases finite_or_infinite (Subgroup.zpowers ((QuotientGroup.mk' N) t)) with
  | inr hinfinite =>
    let := hinfinite
    exact virtualSolvableFiniteDimension_of_nilpotent_contractor N t ht hbase hQ
  | inl hfinite =>
    let := hfinite
    obtain ⟨r, hr, hpow⟩ := (isOfFinOrder_of_finite (quotientLetter N t)).exists_pow_eq_one
    have htr : t ^ r ∈ N := by
      apply (QuotientGroup.eq_one_iff _).mp
      change (QuotientGroup.mk' N) (t ^ r) = 1
      rw [map_pow]
      exact congrArg (fun x : Subgroup.zpowers ((QuotientGroup.mk' N) t) => (x : G ⧸ N)) hpow
    let : Group.FG (Abelianization N) := finitelyGenerated_of_ascending_base_pow_eq_one
      _ r hr (quotient_conjugation_pow_eq_one N t r htr) hbase
    let : Group.FG N := nilpotent_finitelyGenerated_of_abelianization
    obtain ⟨V, hVindex, hVnil, _, _, hVdim⟩ :=
      exists_endomorphismInvariant_nilpotent_finiteIndex
        (Group.IsNilpotent.isVirtuallyNilpotent (inferInstance : Group.IsNilpotent N))
    let := hVnil
    exact exists_solvable_finiteDimension_of_virtuallyPolycyclic_quotient N
      ⟨V, hVindex, inferInstance, hVdim⟩ hQ

end PolycyclicRecognition

end

end OAI
