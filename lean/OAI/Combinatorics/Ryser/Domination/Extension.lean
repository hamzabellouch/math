import OAI.Combinatorics.Ryser.Domination.Append
import OAI.Combinatorics.Ryser.Domination.Nonempty
import OAI.Combinatorics.Ryser.Domination.Counting

namespace OAI

namespace RyserCoveringCounterexample.Selection

variable {V ι : Type*} [DecidableEq V] [DecidableEq ι]

namespace DominationTrace

variable {G : Graph V} {pool : V → ι} {J : Finset ι} {root : ι} {k : ℕ}

theorem extend [Fintype V] (t : DominationTrace G pool J root k)
    (hroot : root ∉ J)
    (hno : ¬ ∃ U', IsTransversalOn G pool (insert root J) U')
    (hnocert : ¬ DominationCertificate G pool) :
    Nonempty (DominationTrace G pool J root (k + 1)) := by
  classical
  have hnotdom : ¬ DominatesOn G pool t.indices t.vertices := by
    intro hd
    exact hnocert ⟨t.indices, t.vertices, t.indices_nonempty,
      t.vertices_pool_mem, t.card_vertices_le hroot, hd⟩
  unfold DominatesOn at hnotdom
  push Not at hnotdom
  obtain ⟨v, hvpool, hvout, hvfree⟩ := hnotdom
  let candidates : Finset (Finset V) := Finset.univ.filter
    (fun U => IsTransversalOn G pool J U ∧
      ∀ a, a < k → neighborsIn G (t.x a) U = t.y a)
  have hcandidates : candidates.Nonempty := by
    obtain ⟨U, hU, hreal⟩ := t.realized
    exact ⟨U, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hU, hreal⟩⟩
  obtain ⟨U, hUc, hmin⟩ := Finset.exists_min_image candidates
    (fun U => (neighborsIn G v U).card) hcandidates
  have hU := (Finset.mem_filter.mp hUc).2
  have hne := t.neighbors_nonempty hroot hno hU.1 hU.2 hvpool hvfree
  apply t.append_exists v (neighborsIn G v U) hne
  · intro a ha
    apply Finset.disjoint_left.mpr
    intro z hznew hzold
    have hzt : z ∈ t.vertices := by
      change z ∈ t.verticesX ∪ t.verticesY
      exact Finset.mem_union_right _ (mem_verticesY.mpr ⟨a, ha, hzold⟩)
    exact hvfree z hzt (mem_neighborsIn.mp hznew).2
  · exact ⟨U, hU.1, hU.2, rfl⟩
  · intro U' hU' hreal'
    exact hmin U' (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hU', hreal'⟩)
  · exact (t.mem_indices_iff).mp hvpool

end DominationTrace
end RyserCoveringCounterexample.Selection

end OAI
