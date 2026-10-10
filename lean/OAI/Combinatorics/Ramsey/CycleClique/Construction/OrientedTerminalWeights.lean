import OAI.Combinatorics.Ramsey.CycleClique.Construction.NormalizedRepresentatives
import OAI.Combinatorics.Ramsey.CycleClique.Construction.TerminalWeights
import OAI.Combinatorics.Ramsey.CycleClique.Construction.TerminalClassification

namespace OAI

/-! The terminal first-pair and second-triple bounds hold in every
independent orientation of the original system. -/

namespace CycleClique.Construction.ExpandedPathSystem

open scoped Classical

variable {V : Type} [Fintype V] {G : SimpleGraph V} {Q : Finset V} {S : ExpandedPathSystem G Q}

theorem IsOptimal.terminal_oriented_first_ball {k : ℕ}
    (hopt : S.IsOptimal k) (hk : 3 ≤ k) (hQk : Q.card ≤ k)
    (hQ : G.IsClique (Q : Set V)) (hcycle : ¬ HasCycle G (k + 1))
    (hclique : G.cliqueNum ≤ Q.card) (hc : 2 ≤ S.chains.length)
    (hexpand : ∀ v, k + 1 ≤ (closedNeighborhood G {v}).card)
    (p : List V → Bool) {x : V}
    (hx : x ∈ (S.toRaw.completeClique.orientChains p).representatives) :
    Q.card + 1 ≤ (outsideBallFinset G S.ground x 1).card ∧
      HasIndependent (G.induce (outsideBallFinset G S.ground x 1 : Set V)) 2 := by
  let U := S.toRaw.completeClique.orientChains p
  let T := U.normalize
  have hTa : T.amount = S.amount := by simp [T, U]
  have hTe : T.assignedCount = S.assignedCount := by simp [T, U]
  have hTi : T.incident = S.incident := by simp [T, U]
  have hTground : T.ground = S.ground := by
    simp only [T, U, RawPathSystem.normalize_ground, RawPathSystem.orientChains_vertices,
      RawPathSystem.completeClique_vertices]
    change Q ∪ (S.vertices ∪ Q) = Q ∪ S.vertices
    ext v
    simp only [Finset.mem_union]
    tauto
  have hcT : 2 ≤ T.chains.length := by
    have hT := T.assignedCount_add_chains_length
    have hS := S.assignedCount_add_chains_length
    rw [hTe, hTi] at hT
    omega
  have hoptT := hopt.of_amount_count T hTa hTe
  have hxT : x ∈ T.representativeFinset := U.normalize_representative_mem hx
  obtain ⟨hcard, hpair⟩ :=
    hoptT.terminal_first_ball hk hQk hQ hcycle hclique hcT hexpand hxT
  refine ⟨by simpa only [hTground] using hcard, ?_⟩
  convert hpair using 1 <;> rw [hTground]

theorem IsOptimal.terminal_oriented_second_ball (hCE : CEAlphaTwo) {k : ℕ}
    (hopt : S.IsOptimal k) (hk : 5 ≤ k) (hQk : Q.card ≤ k) (ht : 1 ≤ Q.card)
    (hkt : 2 * Q.card ≤ k) (hQ : G.IsClique (Q : Set V))
    (hcycle : ¬ HasCycle G (k + 1)) (hclique : G.cliqueNum ≤ Q.card)
    (hc : 2 ≤ S.chains.length)
    (hexpand : ∀ I : Finset V, G.IsIndepSet (I : Set V) → I.Nonempty →
      k * I.card + 1 ≤ (closedNeighborhood G I).card)
    (p : List V → Bool) {x : V}
    (hx : x ∈ (S.toRaw.completeClique.orientChains p).representatives) :
    HasIndependent (G.induce (outsideBallFinset G S.ground x 2 : Set V)) 3 := by
  have hsingle : ∀ v, k + 1 ≤ (closedNeighborhood G {v}).card := by
    intro v
    simpa using hexpand {v} (by simp) (by simp)
  have hp := (hopt.terminal_oriented_first_ball (by omega) hQk hQ hcycle
    hclique hc hsingle p hx).2
  exact outsideBall_two_triple_of_first_pair hCE hk ht hkt hcycle hclique
    (hopt.ground_card_le hQk) hexpand hp

end CycleClique.Construction.ExpandedPathSystem

end OAI
