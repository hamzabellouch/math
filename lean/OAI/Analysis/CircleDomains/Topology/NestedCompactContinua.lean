import Mathlib.Topology.Separation.Regular
import Mathlib.Topology.Compactness.Compact

namespace OAI

/-! The compact intersection step for limiting level continua. -/
open Set Function
noncomputable section
namespace CircleDomainRigidity

 theorem preconnected_iInter_compact_antitone
    {X : Type*} [TopologicalSpace X] [T2Space X] [NormalSpace X]
    (K : ℕ → Set X) (hK : ∀ n, IsCompact (K n))
    (hc : ∀ n, IsPreconnected (K n)) (hm : Antitone K) :
    IsPreconnected (⋂ n, K n) := by
  have hclosed : IsClosed (⋂ n, K n) := isClosed_iInter (fun n => (hK n).isClosed)
  rw [isPreconnected_iff_subset_of_fully_disjoint_closed hclosed]
  intro a b ha hb hcover hab
  obtain ⟨U, V, hU, hV, haU, hbV, hUV⟩ := normal_separation ha hb hab
  have hdis : Disjoint (K 0 ∩ (U ∪ V)ᶜ) (⋂ n, K n) := by
    apply Set.disjoint_left.mpr
    intro p hp hpK
    exact hp.2 ((hcover hpK).elim (fun h => Or.inl (haU h)) (fun h => Or.inr (hbV h)))
  have hcompact := (hK 0).inter_right (hU.union hV).isClosed_compl
  obtain ⟨n, hn⟩ := hcompact.elim_directed_family_closed K
    (fun n => (hK n).isClosed) hdis hm.directed_ge
  have hKn : K n ⊆ U ∪ V := by
    intro p hp
    by_contra hout
    exact Set.disjoint_left.mp hn ⟨hm (Nat.zero_le n) hp, hout⟩ hp
  rcases (hc n).subset_or_subset hU hV hUV hKn with hleft | hright
  · left
    intro p hp
    rcases hcover hp with hpA | hpB
    · exact hpA
    · exact False.elim (Set.disjoint_left.mp hUV (hleft (mem_iInter.mp hp n)) (hbV hpB))
  · right
    intro p hp
    rcases hcover hp with hpA | hpB
    · exact False.elim (Set.disjoint_left.mp hUV (haU hpA) (hright (mem_iInter.mp hp n)))
    · exact hpB

end CircleDomainRigidity

end

end OAI
