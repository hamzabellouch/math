import OAI.Combinatorics.Ramsey.CycleClique.Construction.RawReverse

namespace OAI

/-! Orient chains independently while retaining every vertex, amount and
assigned path. Singleton components may be reversed without effect. -/

namespace CycleClique.Construction.RawPathSystem

open scoped Classical

variable {V : Type*} {G : SimpleGraph V} {Q : Finset V}

def orientedChain (p : List V → Bool) (l : List V) : List V :=
  if p l then l.reverse else l

theorem orientedChain_perm (p : List V → Bool) (l : List V) :
    (orientedChain p l).Perm l := by
  unfold orientedChain
  split_ifs
  · exact List.reverse_perm l
  · exact .refl _

theorem oriented_flatten_perm (p : List V → Bool) (C : List (List V)) :
    (C.map (orientedChain p)).flatten.Perm C.flatten := by
  induction C with
  | nil => exact .refl _
  | cons l C ih =>
    exact (orientedChain_perm p l).append ih

def orientChains (S : RawPathSystem G Q) (p : List V → Bool) : RawPathSystem G Q where
  chains := S.chains.map (orientedChain p)
  paths := by
    intro l hl
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hl
    refine ⟨(orientedChain_perm p r).nodup_iff.mpr (S.paths r hr).1, ?_⟩
    unfold orientedChain
    split_ifs
    · exact List.isChain_reverse.mpr ((S.paths r hr).2.imp (fun _ _ h => h.symm))
    · exact (S.paths r hr).2
  disjoint := (List.nodup_flatten.mp
    ((oriented_flatten_perm p S.chains).nodup_iff.mpr S.flatten_nodup)).2
  endpoints := by
    intro l hl
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hl
    unfold orientedChain
    split_ifs
    · simpa only [List.head?_reverse, List.getLast?_reverse] using
        And.intro (S.endpoints r hr).2 (S.endpoints r hr).1
    · exact S.endpoints r hr
  no_clique_steps := by
    intro l hl
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hl
    unfold orientedChain
    split_ifs
    · exact List.isChain_reverse.mpr
        ((S.no_clique_steps r hr).imp (fun _ _ h h' => h h'.symm))
    · exact S.no_clique_steps r hr

@[simp] theorem orientChains_vertices (S : RawPathSystem G Q) (p : List V → Bool) :
    (S.orientChains p).vertices = S.vertices := by
  ext v
  simp only [vertices, List.mem_toFinset]
  exact (oriented_flatten_perm p S.chains).mem_iff

@[simp] theorem orientChains_amount (S : RawPathSystem G Q) (p : List V → Bool) :
    (S.orientChains p).amount = S.amount := by
  unfold amount
  rw [orientChains_vertices]

@[simp] theorem orientChains_assignedCount (S : RawPathSystem G Q) (p : List V → Bool) :
    (S.orientChains p).assignedCount = S.assignedCount := by
  unfold assignedCount rawAssignedCount
  change ((S.chains.map (orientedChain p)).map (fun l => chainCliqueCount Q l - 1)).sum = _
  simp only [List.map_map, Function.comp_def]
  apply congrArg List.sum
  apply List.map_congr_left
  intro l hl
  unfold orientedChain
  split_ifs <;> simp only [chainCliqueCount_reverse]

theorem representatives_orientChains_unchanged (S : RawPathSystem G Q) {p : List V → Bool}
    {l : List V} (hl : l ∈ S.chains) (hp : p l = false) {x : V}
    (hx : x ∈ chainRepresentatives Q l) : x ∈ (S.orientChains p).representatives := by
  apply List.mem_flatten.mpr
  refine ⟨chainRepresentatives Q l, ?_, hx⟩
  apply List.mem_map.mpr
  refine ⟨l, ?_, rfl⟩
  apply List.mem_map.mpr
  exact ⟨l, hl, by simp [orientedChain, hp]⟩

theorem representatives_orientChains_terminal (S : RawPathSystem G Q) {p : List V → Bool}
    {l : List V} (hl : l ∈ S.chains) (hp : p l = true) {x : V}
    (hx : x ∈ l.getLast?) : x ∈ (S.orientChains p).representatives := by
  apply chain_head_representative (S.orientChains p) (l := l.reverse)
    (List.mem_map.mpr ⟨l, hl, by simp [orientedChain, hp]⟩)
  simpa only [List.head?_reverse] using hx

end CycleClique.Construction.RawPathSystem

end OAI
