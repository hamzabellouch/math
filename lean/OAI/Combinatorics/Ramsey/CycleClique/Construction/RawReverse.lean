import OAI.Combinatorics.Ramsey.CycleClique.Construction.RepresentativeOutside

namespace OAI

/-! Reverse every oriented chain, retaining the same raw system vertices
and amount. Singleton chains are unaffected. -/

namespace CycleClique.Construction.RawPathSystem

open scoped Classical

variable {V : Type*} {G : SimpleGraph V} {Q : Finset V}

theorem reverse_flatten_perm (C : List (List V)) :
    (C.map List.reverse).flatten.Perm C.flatten := by
  induction C with
  | nil => exact .refl _
  | cons l C ih =>
    simpa using (List.reverse_perm l).append ih

def reverseChains (S : RawPathSystem G Q) : RawPathSystem G Q where
  chains := S.chains.map List.reverse
  paths := by
    intro l hl
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hl
    refine ⟨List.nodup_reverse.mpr (S.paths r hr).1, List.isChain_reverse.mpr ?_⟩
    apply (S.paths r hr).2.imp
    intro a b h
    exact h.symm
  disjoint := (List.nodup_flatten.mp
    ((reverse_flatten_perm S.chains).nodup_iff.mpr S.flatten_nodup)).2
  endpoints := by
    intro l hl
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hl
    simpa only [List.head?_reverse, List.getLast?_reverse] using (S.endpoints r hr).symm
  no_clique_steps := by
    intro l hl
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hl
    apply List.isChain_reverse.mpr
    apply (S.no_clique_steps r hr).imp
    intro a b h hab
    exact h hab.symm

@[simp] theorem reverseChains_vertices (S : RawPathSystem G Q) :
    S.reverseChains.vertices = S.vertices := by
  ext v
  simp only [vertices, reverseChains, List.mem_toFinset]
  exact (reverse_flatten_perm S.chains).mem_iff

@[simp] theorem reverseChains_amount (S : RawPathSystem G Q) :
    S.reverseChains.amount = S.amount := by
  unfold amount
  rw [reverseChains_vertices]

theorem chain_head_representative (S : RawPathSystem G Q) {l : List V} (hl : l ∈ S.chains)
    {x : V} (hx : x ∈ l.head?) : x ∈ S.representatives := by
  apply List.mem_flatten.mpr
  refine ⟨chainRepresentatives Q l, List.mem_map.mpr ⟨l, hl, rfl⟩, ?_⟩
  cases l with
  | nil => simp at hx
  | cons a l =>
    have he : a = x := by simpa using hx
    simp [chainRepresentatives, he]

theorem reversed_terminal_representative (S : RawPathSystem G Q)
    {l : List V} (hl : l ∈ S.chains) {x : V} (hx : x ∈ l.getLast?) :
    x ∈ S.reverseChains.representatives := by
  apply chain_head_representative S.reverseChains
    (List.mem_map.mpr ⟨l, hl, rfl⟩ : l.reverse ∈ S.reverseChains.chains)
  simpa only [List.head?_reverse] using hx

theorem completed_unused_representative (S : ExpandedPathSystem G Q) {x : V}
    (hxQ : x ∈ Q) (hxS : x ∉ S.vertices) :
    x ∈ S.toRaw.completeClique.representatives ∧
      x ∈ S.toRaw.completeClique.reverseChains.representatives := by
  have hmem : [x] ∈ S.toRaw.completeClique.chains := by
    change [x] ∈ S.chains ++ (Q \ S.toRaw.vertices).toList.map (fun v => [v])
    apply List.mem_append_right
    apply List.mem_map.mpr
    exact ⟨x, Finset.mem_toList.mpr (Finset.mem_sdiff.mpr ⟨hxQ, hxS⟩), rfl⟩
  exact ⟨chain_head_representative _ hmem (by simp), reversed_terminal_representative _ hmem (by simp)⟩

end CycleClique.Construction.RawPathSystem

namespace CycleClique.Construction
open scoped Classical

variable {V : Type*} {Q : Finset V}

theorem chainRepresentatives_clique_mem_head {l : List V} {x : V}
    (hsteps : l.IsChain (fun a b => ¬ (a ∈ Q ∧ b ∈ Q)))
    (hx : x ∈ chainRepresentatives Q l) (hxQ : x ∈ Q) : x ∈ l.head? := by
  cases l with
  | nil => simp [chainRepresentatives] at hx
  | cons a l =>
    simp only [chainRepresentatives, List.mem_cons] at hx
    rcases hx with rfl | hx
    · simp
    · exact False.elim (representativesFrom_outside hsteps x hx hxQ)

end CycleClique.Construction

end OAI
