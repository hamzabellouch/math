import OAI.Analysis.CircleDomains.Selection.OuterContours

namespace OAI

/-! Two connected local sides of a Jordan boundary lie on opposite
sides. The proof uses density and regular openness of the actual Jordan disk. -/
open Set Function Filter
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

lemma connected_disjoint_jordan_boundary {S : Set ℂ} (hS : IsPreconnected S)
    (H : ℂ ≃ₜ ℂ) (hd : Disjoint S (frontier (jordanInterior H))) :
    S ⊆ jordanInterior H ∨ S ⊆ (closure (jordanInterior H))ᶜ := by
  apply hS.subset_or_subset (jordanInterior_isOpen H) isClosed_closure.isOpen_compl
  · exact Set.disjoint_left.mpr (fun z hz hz' => hz' (subset_closure hz))
  · intro z hz
    by_cases hzin : z ∈ jordanInterior H
    · exact Or.inl hzin
    · right
      intro hzc
      apply Set.disjoint_left.mp hd hz
      rw [frontier, (jordanInterior_isOpen H).interior_eq]
      exact ⟨hzc, hzin⟩

lemma jordan_local_sides (H : ℂ ≃ₜ ℂ) {N S T : Set ℂ} {x : ℂ}
    (hN : IsOpen N) (hxN : x ∈ N) (hx : x ∈ frontier (jordanInterior H))
    (hS : IsPreconnected S) (hT : IsPreconnected T)
    (hSf : Disjoint S (frontier (jordanInterior H)))
    (hTf : Disjoint T (frontier (jordanInterior H)))
    (hcover : N ⊆ closure (S ∪ T)) :
    (S ⊆ jordanInterior H ∧ T ⊆ (closure (jordanInterior H))ᶜ) ∨
      (T ⊆ jordanInterior H ∧ S ⊆ (closure (jordanInterior H))ᶜ) := by
  have hxin : x ∉ jordanInterior H := by
    intro hi
    exact hx.2 ((jordanInterior_isOpen H).interior_eq.symm ▸ hi)
  rcases connected_disjoint_jordan_boundary hS H hSf with hSi | hSo <;>
    rcases connected_disjoint_jordan_boundary hT H hTf with hTi | hTo
  · have hc : N ⊆ closure (jordanInterior H) :=
      hcover.trans (closure_mono (union_subset hSi hTi))
    have hi : x ∈ interior (closure (jordanInterior H)) :=
      mem_interior_iff_mem_nhds.mpr (Filter.mem_of_superset (hN.mem_nhds hxN) hc)
    rw [interior_closure_jordanInterior] at hi
    exact (hxin hi).elim
  · exact Or.inl ⟨hSi, hTo⟩
  · exact Or.inr ⟨hTi, hSo⟩
  · have hc : N ⊆ (jordanInterior H)ᶜ := by
      have hh := hcover.trans (closure_mono (union_subset hSo hTo))
      simpa only [closure_compl, interior_closure_jordanInterior] using hh
    obtain ⟨y, hyN, hyJ⟩ := mem_closure_iff.1 hx.1 N hN hxN
    exact (hc hyN hyJ).elim

end CircleDomainRigidity

end

end OAI
