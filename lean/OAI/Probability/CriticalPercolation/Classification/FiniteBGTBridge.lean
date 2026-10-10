import Mathlib

namespace OAI

section
noncomputable section
open Set Function
open scoped Pointwise

namespace CriticalPercolation.CompactQuotient
variable {A : Type*} [Group A]

lemma nilpotent_image_of_nilpotent_subquotient (H N : Subgroup A) [H.Normal]
    [Group.IsNilpotent (N ⧸ H.subgroupOf N)] :
    Group.IsNilpotent (N.map (QuotientGroup.mk' H)) := by
  let f : N →* N.map (QuotientGroup.mk' H) := (QuotientGroup.mk' H).subgroupMap N
  have hker : H.subgroupOf N≤f.ker := by
    intro n hn
    apply Subtype.ext
    exact (QuotientGroup.eq_one_iff _).mpr hn
  let ψ := QuotientGroup.lift (H.subgroupOf N) f hker
  have hs : Surjective ψ := by
    intro y
    obtain ⟨n,rfl⟩ := (QuotientGroup.mk' H).subgroupMap_surjective N y
    exact ⟨QuotientGroup.mk' (H.subgroupOf N) n,rfl⟩
  exact Group.nilpotent_of_surjective ψ hs

lemma index_image_of_subquotient (H N : Subgroup A) [H.Normal] (hHN : H≤N) :
    (N.map (QuotientGroup.mk' H)).index=N.index := by
  apply N.index_map_eq QuotientGroup.mk_surjective
  rw [QuotientGroup.ker_mk']
  exact hHN

theorem finite_by_nilpotent_of_BGT_output (S : Set A) (hS : S.Finite) (n : ℕ)
    (H N : Subgroup A) [H.Normal] (hHN : H≤N) (hH : (H : Set A)⊆S^(4*n))
    [Group.IsNilpotent (N ⧸ H.subgroupOf N)] (hN : N.index≠0) :
    (H : Set A).Finite ∧
      ∃ M : Subgroup (A ⧸ H), Group.IsNilpotent M ∧ M.index≠0 := by
  have hpow : ∀ k : ℕ, (S^k).Finite := by
    intro k
    induction k with
    | zero => simpa only [pow_zero] using (Set.finite_one : (1 : Set A).Finite)
    | succ k ih => simpa only [pow_succ] using ih.mul hS
  refine ⟨(hpow (4*n)).subset hH,N.map (QuotientGroup.mk' H),
    nilpotent_image_of_nilpotent_subquotient H N,?_⟩
  rw [index_image_of_subquotient H N hHN]
  exact hN

end CriticalPercolation.CompactQuotient
end
end

end OAI
