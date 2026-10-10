import OAI.GroupTheory.PolycyclicRecognition.Algebra.AbelianCyclicTorsion
import OAI.GroupTheory.PolycyclicRecognition.Algebra.FiniteTorsionPowerSubgroup
import OAI.GroupTheory.PolycyclicRecognition.Algebra.AbelianCyclicFiniteDimension
import OAI.GroupTheory.PolycyclicRecognition.Algebra.VirtualSolvableDimension

namespace OAI

/-! # The FP-infinity finiteness endgame for abelian-by-cyclic groups

The kernel need not be finitely generated. Its torsion and all prime-field
reductions are controlled by the ambient finite projective resolutions.
-/

noncomputable section
namespace PolycyclicRecognition
open CategoryTheory
open scoped IsMulCommutative
variable {G : Type} [Group G] [Group.FG G]
  (N : Subgroup G) [N.Normal] [IsMulCommutative N] [IsCyclic (G ⧸ N)]

theorem abelian_cyclic_kernel_characteristic_finiteIndex_torsionFree (h : TypeFPInfinity G) :
    ∃ K : Subgroup N, K.Characteristic ∧ K.FiniteIndex ∧ HasNoNontrivialTorsion K := by
  let := abelian_cyclic_kernel_torsion_finite N h
  let n := Nat.card (CommGroup.torsion N)
  have hn : n ≠ 0 := Nat.ne_of_gt Nat.card_pos
  let := abelian_cyclic_integer_reduction_finite N h n hn
  exact ⟨(powMonoidHom n : N →* N).range, abelianPowerRange_characteristic N n,
    abelianPowerRange_finiteIndex N n, abelianPowerRange_torsionFree N⟩

include N in
theorem abelian_cyclic_virtual_finite_dimension (h : TypeFPInfinity G) :
    ∃ V : Subgroup G, V.FiniteIndex ∧ Group.IsSolvable V ∧
      HasFiniteIntegralCohomologicalDimension V := by
  obtain ⟨K, hKchar, hKindex, hKtf⟩ :=
    abelian_cyclic_kernel_characteristic_finiteIndex_torsionFree N h
  let := hKchar
  let := hKindex
  let : CommGroup N := inferInstance
  let : Group.IsSolvable K := inferInstance
  let : Countable G := countable_of_group_fg G
  obtain ⟨d, hd⟩ := abelian_cyclic_kernel_finite_rank N h
  have hKr : Module.rank ℤ (Additive K) ≤ d :=
    ((K.subtype.toAdditive.toIntLinearMap).rank_le_of_injective K.subtype_injective).trans hd
  let hKd := abelian_cohomologicalDimension_of_rank d hKr hKtf
  let A : Subgroup G := K.map N.subtype
  have hA := solvable_finiteDimension_of_equiv
    (K.equivMapOfInjective N.subtype N.subtype_injective)
    (show HasFiniteIntegralCohomologicalDimension K from ⟨d + 1, hKd⟩)
  let := hA.1
  cases finite_or_infinite (G ⧸ N) with
  | inl hfinite =>
    let := hfinite
    let : N.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
    refine ⟨A, ⟨?_⟩, hA.1, hA.2⟩
    change (K.map N.subtype).index ≠ 0
    rw [Subgroup.index_map_subtype]
    exact mul_ne_zero hKindex.index_ne_zero (Subgroup.FiniteIndex.index_ne_zero (H := N))
  | inr hinfinite =>
    let := hinfinite
    let e : G ⧸ N ≃* Multiplicative ℤ := intCyclicMulEquiv.symm
    let q : G →* Multiplicative ℤ := e.toMonoidHom.comp (QuotientGroup.mk' N)
    have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective N)
    obtain ⟨t, ht⟩ := hq (Multiplicative.ofAdd 1)
    have hAq : A ≤ q.ker := by
      rintro _ ⟨a, _, rfl⟩
      change e (QuotientGroup.mk' N a) = 1
      have ha : (QuotientGroup.mk' N) a = 1 :=
        (QuotientGroup.eq_one_iff (a : G)).mpr a.property
      exact (congrArg e ha).trans e.map_one
    have hnorm : t ∈ Subgroup.normalizer A := Subgroup.mem_normalizer_iff.mpr
      (fun _ => ⟨fun h => Subgroup.Normal.conj_mem inferInstance _ h t,
        fun h => by simpa [mul_assoc] using
          Subgroup.Normal.conj_mem (inferInstance : A.Normal) _ h t⁻¹⟩)
    let V : Subgroup G := A ⊔ Subgroup.zpowers t
    have hVindex : V.FiniteIndex := finiteIndex_of_kernel_cover N K V le_sup_left (by
      intro g
      refine ⟨t ^ (q g).toAdd, (show Subgroup.zpowers t ≤ V from le_sup_right)
        (Subgroup.zpow_mem_zpowers t _), ?_⟩
      apply e.injective
      change q (t ^ (q g).toAdd) = q g
      apply Multiplicative.toAdd.injective
      simp [map_zpow, ht])
    exact ⟨V, hVindex, cyclicJoin_solvable q t ht A hAq hnorm,
      cyclicJoin_finiteDimension q t ht A hAq hnorm hA.2⟩

end PolycyclicRecognition

end

end OAI
