import OAI.Combinatorics.Ramsey.CycleClique.Construction.TerminalRepresentative
import OAI.Combinatorics.Ramsey.CycleClique.Construction.RepresentativePacking

namespace OAI

/-! Manuscript grow:short: at least nine representatives force a short
outside path, for every orientation of an optimal expanded system. -/

namespace CycleClique.Construction.ExpandedPathSystem

open scoped Classical

variable {V : Type} [Fintype V] {G : SimpleGraph V} {Q : Finset V} {S : ExpandedPathSystem G Q}

theorem IsOptimal.short_representative_path (hCE : CEAlphaTwo) {k : ℕ}
    (hopt : S.IsOptimal k) (hk : 5 ≤ k) (ht : 9 ≤ Q.card)
    (hQk : Q.card ≤ k) (hkQ : k ≤ 2 * Q.card + 1)
    (hQ : G.IsClique (Q : Set V)) (hcycle : ¬ HasCycle G (k + 1))
    (hclique : G.cliqueNum ≤ Q.card) (hbound : IndependenceBound G k)
    (hexpand : ∀ I : Finset V, G.IsIndepSet (I : Set V) → I.Nonempty →
      k * I.card + 1 ≤ (closedNeighborhood G I).card) :
    ∃ x ∈ S.representativeFinset, ∃ y ∈ S.representativeFinset,
      x ≠ y ∧ ∃ d, 2 ≤ d ∧ d ≤ 6 ∧ OutsidePath G (S.ground : Set V) x y d := by
  have hRcard := S.representativeFinset_card
  have hRX := S.representativeFinset_subset_ground
  have hXk := hopt.ground_card_le hQk
  have hclique' : G.cliqueNum ≤ S.representativeFinset.card := by omega
  have hsingle : ∀ v, k + 1 ≤ (closedNeighborhood G {v}).card := by
    intro v
    simpa using hexpand {v} (by simp) (by simp)
  have hf : ∀ x ∈ S.representativeFinset, ∀ y ∈ S.representativeFinset,
      x ≠ y → ¬ OutsidePath G (S.ground : Set V) x y 1 := by
    intro x hx y hy hne
    exact hopt.representativeFinset_one_exclusion (by omega) hQk hQ hcycle hx hy hne
  have hshort : ∃ x ∈ S.representativeFinset, ∃ y ∈ S.representativeFinset,
      x ≠ y ∧ ∃ d, 1 ≤ d ∧ d ≤ 6 ∧ OutsidePath G (S.ground : Set V) x y d := by
    by_cases hlarge : k < 2 * S.representativeFinset.card
    · exact exists_short_path_of_twice_card_gt hbound hRX hXk hclique' hsingle hlarge
    · have hRk : S.representativeFinset.card < k := by omega
      have hspecial : ∃ a ∈ S.representativeFinset, ∃ b ∈ S.representativeFinset,
          a ≠ b ∧ ¬ G.IsClique (outsideBallFinset G S.ground a 1 : Set V) ∧
          ¬ G.IsClique (outsideBallFinset G S.ground b 1 : Set V) := by
        by_cases he : 2 ≤ S.assignedCount
        · exact hopt.two_interior_nonclique_balls (by omega) hQk hQ hcycle hclique hsingle he
        · by_cases he0 : S.assignedCount = 0
          · have hL := S.amount_eq_zero_of_assignedCount_eq_zero he0
            have hXcard : S.ground.card < k := by rw [ground_card, hL]; omega
            have hnonclique : ∀ x ∈ S.representativeFinset,
                ¬ G.IsClique (outsideBallFinset G S.ground x 1 : Set V) := by
              intro x hx hC
              have hd := representative_ball_one hx hRX hXk hsingle (hf x hx)
              have hc := hC.card_le_cliqueNum.trans hclique'
              omega
            have htwo : 1 < S.representativeFinset.card := by omega
            obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp htwo
            exact ⟨a, ha, b, hb, hab, hnonclique a ha, hnonclique b hb⟩
          · have he1 : S.assignedCount = 1 := by omega
            exact hopt.two_unused_nonclique_balls (by omega) hQk hQ hcycle hclique hsingle he1 (by omega)
      exact exists_short_path_of_two_noncliques hCE hk hbound hRX hXk hRk (by omega)
        hcycle hclique' hexpand hspecial
  obtain ⟨x, hx, y, hy, hxy, d, hd, hdb, hp⟩ := hshort
  have hdne : d ≠ 1 := by intro he; subst d; exact hf x hx y hy hxy hp
  exact ⟨x, hx, y, hy, hxy, d, by omega, hdb, hp⟩

end CycleClique.Construction.ExpandedPathSystem

end OAI
