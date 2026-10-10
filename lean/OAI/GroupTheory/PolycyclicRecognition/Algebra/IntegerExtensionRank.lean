import OAI.GroupTheory.PolycyclicRecognition.Finiteness.PolyZDuality
import Mathlib.GroupTheory.Rank

namespace OAI

/-! # A generator bound for an infinite cyclic extension -/

noncomputable section
namespace PolycyclicRecognition

variable {G : Type} [Group G] [Group.FG G]

theorem rank_le_kernel_rank_add_one (q : G →* Multiplicative ℤ)
    (t : G) (ht : q t = Multiplicative.ofAdd 1) [Group.FG q.ker] :
    Group.rank G ≤ Group.rank q.ker + 1 := by
  classical
  obtain ⟨S, hcard, hS⟩ := Group.rank_spec q.ker
  let T : Finset G := S.image Subtype.val ∪ {t}
  let H := Subgroup.closure (T : Set G)
  have hker : q.ker ≤ H := by
    have hmap : (Subgroup.closure (S : Set q.ker)).map q.ker.subtype ≤ H := by
      rw [MonoidHom.map_closure]
      rw [Subgroup.closure_le]
      rintro _ ⟨a, ha, rfl⟩
      apply Subgroup.subset_closure
      exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ ha)
    simpa only [hS, ← MonoidHom.range_eq_map, Subgroup.range_subtype] using hmap
  have htH : t ∈ H :=
    Subgroup.subset_closure (Finset.mem_union_right _ (Finset.mem_singleton_self _))
  have hH : H = ⊤ := by
    apply top_unique
    intro g _
    let z := (q g).toAdd
    have hzt : q (t ^ z) = q g := by
      rw [map_zpow, ht]
      apply Multiplicative.toAdd.injective
      simp [z]
    have hk : g * (t ^ z)⁻¹ ∈ q.ker := by
      change q (g * (t ^ z)⁻¹) = 1
      rw [map_mul, map_inv, hzt, mul_inv_cancel]
    have hprod := H.mul_mem (hker hk) (H.zpow_mem htH z)
    simpa only [mul_assoc, inv_mul_cancel, mul_one] using hprod
  calc
    Group.rank G ≤ T.card := Group.rank_le hH
    _ ≤ (S.image Subtype.val).card + ({t} : Finset G).card := Finset.card_union_le _ _
    _ ≤ S.card + 1 := by rw [Finset.card_singleton]; exact Nat.add_le_add_right Finset.card_image_le 1
    _ = Group.rank q.ker + 1 := by rw [hcard]

theorem rank_le_add_one_of_infiniteCyclicQuotient
    (N : Subgroup G) [N.Normal] [Group.FG N]
    [IsCyclic (G ⧸ N)] [Infinite (G ⧸ N)] : Group.rank G ≤ Group.rank N + 1 := by
  let e : Multiplicative ℤ ≃* G ⧸ N := intCyclicMulEquiv
  let q : G →* Multiplicative ℤ := e.symm.toMonoidHom.comp (QuotientGroup.mk' N)
  have hker : q.ker = N := by
    ext g
    change e.symm (QuotientGroup.mk' N g) = 1 ↔ g ∈ N
    rw [← e.symm.map_one, e.symm.injective.eq_iff]
    exact QuotientGroup.eq_one_iff g
  obtain ⟨t, ht⟩ := QuotientGroup.mk'_surjective N (e (Multiplicative.ofAdd 1))
  have hqt : q t = Multiplicative.ofAdd 1 := by
    change e.symm (QuotientGroup.mk' N t) = _
    rw [ht, e.symm_apply_apply]
  let : Group.FG q.ker := hker.symm ▸ (inferInstance : Group.FG N)
  exact (rank_le_kernel_rank_add_one q t hqt).trans_eq
    (congrArg (fun r => r + 1) (Subgroup.rank_congr hker))

end PolycyclicRecognition

end

end OAI
