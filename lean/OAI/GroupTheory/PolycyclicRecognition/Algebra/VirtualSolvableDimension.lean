import OAI.GroupTheory.PolycyclicRecognition.Algebra.CyclicJoinDimension
import OAI.GroupTheory.PolycyclicRecognition.Algebra.CharacteristicFiniteIndex
import OAI.GroupTheory.PolycyclicRecognition.Algebra.TorsionFreeCyclicExtension

namespace OAI

/-! # Finite-index solvable dimension bounds along cyclic extensions -/

noncomputable section
namespace PolycyclicRecognition
open CategoryTheory
variable {G J : Type} [Group G] [Group J]

theorem solvable_finiteDimension_of_equiv (e : G ≃* J)
    [Group.IsSolvable G] (hG : HasFiniteIntegralCohomologicalDimension G) :
    Group.IsSolvable J ∧ HasFiniteIntegralCohomologicalDimension J := by
  obtain ⟨d, hd⟩ := hG
  let := hd
  exact ⟨Group.isSolvable_of_isSolvable_injective (f := e.symm.toMonoidHom) e.symm.injective,
    d, cohomologicalDimension_le_of_equiv e d⟩

theorem exists_solvable_finiteDimension_of_equiv (e : G ≃* J)
    (hG : ∃ V : Subgroup G, V.FiniteIndex ∧ Group.IsSolvable V ∧
      HasFiniteIntegralCohomologicalDimension V) :
    ∃ W : Subgroup J, W.FiniteIndex ∧ Group.IsSolvable W ∧
      HasFiniteIntegralCohomologicalDimension W := by
  obtain ⟨V, hVindex, hVsolv, hVdim⟩ := hG
  let := hVindex
  let := hVsolv
  have hW := solvable_finiteDimension_of_equiv
    (V.equivMapOfInjective e.toMonoidHom e.injective) hVdim
  exact ⟨V.map e.toMonoidHom, Subgroup.FiniteIndex.map_of_surjective V e.surjective,
    hW.1, hW.2⟩

theorem exists_solvable_finiteDimension_of_finiteIndex (H : Subgroup G) [H.FiniteIndex]
    (hH : ∃ V : Subgroup H, V.FiniteIndex ∧ Group.IsSolvable V ∧
      HasFiniteIntegralCohomologicalDimension V) :
    ∃ W : Subgroup G, W.FiniteIndex ∧ Group.IsSolvable W ∧
      HasFiniteIntegralCohomologicalDimension W := by
  obtain ⟨V, hVindex, hVsolv, hVdim⟩ := hH
  let := hVindex
  let := hVsolv
  have hW := solvable_finiteDimension_of_equiv
    (V.equivMapOfInjective H.subtype H.subtype_injective) hVdim
  refine ⟨V.map H.subtype, ⟨?_⟩, hW.1, hW.2⟩
  rw [Subgroup.index_map_subtype]
  exact mul_ne_zero hVindex.index_ne_zero (Subgroup.FiniteIndex.index_ne_zero (H := H))

theorem exists_solvable_finiteDimension_of_cyclic_extension
    (N : Subgroup G) [N.Normal] [Group.FG N] [IsCyclic (G ⧸ N)]
    (hN : ∃ U : Subgroup N, U.FiniteIndex ∧ Group.IsSolvable U ∧
      HasFiniteIntegralCohomologicalDimension U) :
    ∃ V : Subgroup G, V.FiniteIndex ∧ Group.IsSolvable V ∧
      HasFiniteIntegralCohomologicalDimension V := by
  obtain ⟨U, hUindex, hUsolv, d, hUdim⟩ := hN
  let := hUindex
  let := hUsolv
  let := hUdim
  obtain ⟨K, hKU, hKchar, hKindex⟩ := exists_characteristic_finiteIndex_le U
  let := hKchar
  let := hKindex
  let : Group.IsSolvable K := Group.isSolvable_of_isSolvable_injective
    (Subgroup.inclusion_injective hKU)
  have hKdim : HasFiniteIntegralCohomologicalDimension K :=
    ⟨d, cohomologicalDimension_le_of_injective (Subgroup.inclusion hKU)
      (Subgroup.inclusion_injective hKU) d⟩
  let A : Subgroup G := K.map N.subtype
  have hA := solvable_finiteDimension_of_equiv
    (K.equivMapOfInjective N.subtype N.subtype_injective) hKdim
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
