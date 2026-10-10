import Mathlib
import OAI.Probability.CriticalPercolation.Growth.CosetTransfer

namespace OAI

section
noncomputable section
open Set Function
open scoped Classical Pointwise

namespace CriticalPercolation.RelativeGrowth
variable {A B : Type*} [Group A] [Group B]

lemma Bounded.image_trans {S : Set B} {T U : Set A} (f : A →* B)
    (hT : Bounded S (f '' T)) (hU : Bounded T U) : Bounded S (f '' U) := by
  obtain ⟨L,hL⟩ := hT
  obtain ⟨n,hn⟩ := hU
  refine ⟨L*n,?_⟩
  rw [pow_mul]
  apply Set.Subset.trans (Set.image_mono hn)
  rw [Set.image_pow]
  exact Set.pow_subset_pow_left hL

lemma finiteIndex_generators_containing_stabilizer (K : Subgroup A) (S : Set A)
    (h1 : (1:A)∈S) (hi : S⁻¹=S) (hgen : Subgroup.closure S=⊤)
    (hK : Bounded S (K:Set A)) (H : Subgroup A) [H.FiniteIndex] :
    ∃ T : Set H, (1:H)∈T ∧ T⁻¹=T ∧ Subgroup.closure T=⊤ ∧
      Bounded S (H.subtype '' T) ∧ (K.subgroupOf H:Set H)⊆T := by
  obtain ⟨U,hU1,hUi,hUgen,hUb⟩ := finiteIndex_bounded_generators S h1 hi hgen H
  let T := (K.subgroupOf H:Set H)∪U
  refine ⟨T,Or.inr hU1,?_,?_,?_,Set.subset_union_left⟩
  · simp only [T,Set.union_inv,inv_coe_set,hUi]
  · apply top_unique
    rw [←hUgen]
    exact Subgroup.closure_mono Set.subset_union_right
  · rw [Set.image_union]
    exact (hK.mono (by rintro _ ⟨k,hk,rfl⟩; exact hk)).union h1 hUb

lemma normalizer_of_normal_subgroup (H : Subgroup A) (N : Subgroup H) [N.Normal] :
    H≤Subgroup.normalizer ((N.map H.subtype):Set A) := by
  have hh := N.le_normalizer_map H.subtype
  rwa [Subgroup.normalizer_eq_top,←MonoidHom.range_eq_map,Subgroup.range_subtype] at hh

lemma relIndex_map_subgroupOf_nonzero (K H : Subgroup A) [H.FiniteIndex]
    (N : Subgroup H) (hN : N.relIndex (K.subgroupOf H)≠0) :
    (N.map H.subtype).relIndex K≠0 := by
  have he : (K.subgroupOf H).map H.subtype=K⊓H := by
    rw [Subgroup.subgroupOf,Subgroup.map_comap_eq,Subgroup.range_subtype,inf_comm]
  have hfirst : (N.map H.subtype).relIndex (K⊓H)≠0 := by
    rw [←he,Subgroup.relIndex_map_map_of_injective N (K.subgroupOf H) H.subtype_injective]
    exact hN
  apply Subgroup.relIndex_ne_zero_trans hfirst
  rw [Subgroup.inf_relIndex_left]
  exact fun h => (inferInstance : H.FiniteIndex).index_ne_zero (Subgroup.index_eq_zero_of_relIndex_eq_zero h)

end CriticalPercolation.RelativeGrowth
end
end

end OAI
