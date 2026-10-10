import OAI.GroupTheory.PolycyclicRecognition.Algebra.PolyZExtension
import OAI.GroupTheory.PolycyclicRecognition.Algebra.PolycyclicTorsionFree

namespace OAI

/-! # Finite-index poly-Z subgroups of polycyclic groups -/

noncomputable section
namespace PolycyclicRecognition

open scoped Pointwise
open ChromaticCyclic
variable {G : Type} [Group G]

theorem infiniteCyclic_torsionFree [IsCyclic G] [Infinite G] :
    HasNoNontrivialTorsion G := by
  have ht : HasNoNontrivialTorsion (Multiplicative ℤ) := by
    intro g n hn hg
    apply Multiplicative.toAdd.injective
    change g.toAdd = 0
    have h : (n : ℤ) * g.toAdd = 0 := by
      simpa using congrArg Multiplicative.toAdd hg
    exact (mul_eq_zero.mp h).resolve_left (by exact_mod_cast hn)
  exact ht.of_injective (intCyclicMulEquiv.symm.toMonoidHom) intCyclicMulEquiv.symm.injective

theorem polyZ_finiteIndex_of_cyclic_extension
    (N : Subgroup G) [N.Normal] [Group.FG N] [IsCyclic (G ⧸ N)]
    (hN : ∃ L : Subgroup N, L.FiniteIndex ∧ IsPolyZ L) :
    ∃ H : Subgroup G, H.FiniteIndex ∧ IsPolyZ H := by
  obtain ⟨L, hLi, hLz⟩ := hN
  let := hLi
  obtain ⟨K, hKL, hKc, hKi⟩ := exists_characteristic_finiteIndex_le L
  let := hKc
  let := hKi
  have hKz : IsPolyZ K := hLz.of_injective (Subgroup.inclusion hKL)
    (Subgroup.inclusion_injective hKL)
  let A : Subgroup G := K.map N.subtype
  have hAz : IsPolyZ A := hKz.of_equiv (K.equivMapOfInjective N.subtype N.subtype_injective)
  let q := QuotientGroup.mk' N
  have hAq : A ≤ q.ker := by
    rintro a ⟨k, hk, rfl⟩
    change q k = 1
    exact (QuotientGroup.eq_one_iff (k : G)).mpr k.property
  cases finite_or_infinite (G ⧸ N) with
  | inl hfin =>
    let := hfin
    let : N.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
    have hAi : A.FiniteIndex := ⟨by
      change (K.map N.subtype).index ≠ 0
      rw [Subgroup.index_map_subtype]
      exact mul_ne_zero hKi.index_ne_zero (Subgroup.FiniteIndex.index_ne_zero (H := N))⟩
    exact ⟨A, hAi, hAz⟩
  | inr hinf =>
    let := hinf
    obtain ⟨z, hz⟩ := isCyclic_iff_exists_zpowers_eq_top.mp
      (inferInstance : IsCyclic (G ⧸ N))
    obtain ⟨g, hg⟩ := QuotientGroup.mk'_surjective N z
    have hz0 : orderOf z = 0 := orderOf_eq_card_of_zpowers_eq_top hz
      |>.trans (Nat.card_eq_zero_of_infinite)
    have hzinj : Function.Injective (fun k : ℤ => z ^ k) :=
      injective_zpow_iff_not_isOfFinOrder.mpr (orderOf_eq_zero_iff.mp hz0)
    let H : Subgroup G := A ⊔ Subgroup.zpowers g
    have hHi : H.FiniteIndex := finiteIndex_of_kernel_cover N K H le_sup_left (by
      intro x
      have hx : q x ∈ Subgroup.zpowers z := hz.ge (Subgroup.mem_top _)
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hx
      refine ⟨g ^ k, (show Subgroup.zpowers g ≤ H from le_sup_right)
        (Subgroup.zpow_mem_zpowers g k), ?_⟩
      change q (g ^ k) = q x
      rw [map_zpow, hg, hk])
    have hker (x : H) (hx : q (x : G) = 1) : (x : G) ∈ A := by
      have hmem : (x : G) ∈ (A : Set G) * (Subgroup.zpowers g : Set G) := by
        rw [← Subgroup.normal_mul]
        exact x.property
      obtain ⟨a, ha, b, hb, hab⟩ := hmem
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
      have he : z ^ k = z ^ (0 : ℤ) := by
        rw [zpow_zero, ← hx, ← hab, map_mul, hAq ha, one_mul, map_zpow, hg]
      have hk : k = 0 := hzinj he
      have hxa : (x : G) = a := by simpa [hk] using hab.symm
      rwa [hxa]
    let A' : Subgroup H := A.subgroupOf H
    let f : H ⧸ A' →* G ⧸ N :=
      QuotientGroup.lift A' (q.comp H.subtype) (by
        intro x hx
        exact hAq hx)
    have hf : Function.Injective f := by
      apply f.ker_eq_bot_iff.mp
      apply le_antisymm ?_ bot_le
      intro x hx
      obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective A' x
      exact (QuotientGroup.eq_one_iff x).mpr (hker x hx)
    let : IsCyclic (H ⧸ A') := isCyclic_of_injective f hf
    have hA'z : IsPolyZ A' := hAz.of_equiv
      (Subgroup.subgroupOfEquivOfLe (show A ≤ H from le_sup_left)).symm
    exact ⟨H, hHi, isPolyZ_of_normal_cyclic_quotient A' hA'z
      ((infiniteCyclic_torsionFree (G := G ⧸ N)).of_injective f hf)⟩

end PolycyclicRecognition

end

end OAI
