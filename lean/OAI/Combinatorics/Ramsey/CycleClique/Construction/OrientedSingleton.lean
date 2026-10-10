import OAI.Combinatorics.Ramsey.CycleClique.Construction.NormalizedIncident

namespace OAI

/-! Singleton components of every orientation are exactly the missing
clique vertices of the original expanded system. -/

namespace CycleClique.Construction.ExpandedPathSystem

open scoped Classical

variable {V : Type*} {G : SimpleGraph V} {Q : Finset V}

theorem oriented_complete_singleton_iff (S : ExpandedPathSystem G Q)
    (p : List V → Bool) {l : List V} {x : V}
    (hl : l ∈ (S.toRaw.completeClique.orientChains p).chains) (hx : x ∈ l) :
    l.length = 1 ↔ x ∉ S.vertices := by
  classical
  change l ∈ S.toRaw.completeClique.chains.map (RawPathSystem.orientedChain p) at hl
  obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hl
  have hp := RawPathSystem.orientedChain_perm p m
  have hmx : x ∈ m := hp.mem_iff.mp hx
  change m ∈ S.chains ++ (Q \ S.toRaw.vertices).toList.map (fun v => [v]) at hm
  rcases List.mem_append.mp hm with hm | hm
  · have hxS : x ∈ S.vertices :=
      List.mem_toFinset.mpr (List.mem_flatten.mpr ⟨m, hm, hmx⟩)
    have hn := S.nontrivial m hm
    constructor
    · intro hlen
      have hh := hp.length_eq
      omega
    · intro hnot
      exact False.elim (hnot hxS)
  · obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hm
    have hxv : x = v := by simpa using hmx
    subst x
    have hvnot : v ∉ S.vertices := (Finset.mem_sdiff.mp (Finset.mem_toList.mp hv)).2
    have hlen : (RawPathSystem.orientedChain p [v]).length = 1 := hp.length_eq
    exact ⟨fun _ => hvnot, fun _ => hlen⟩

theorem oriented_complete_tail_nil_iff (S : ExpandedPathSystem G Q)
    (p : List V → Bool) {B : List V} {x : V}
    (hl : x :: B ∈ (S.toRaw.completeClique.orientChains p).chains) :
    B = [] ↔ x ∉ S.vertices := by
  simpa using S.oriented_complete_singleton_iff p hl (by simp)

end CycleClique.Construction.ExpandedPathSystem

end OAI
