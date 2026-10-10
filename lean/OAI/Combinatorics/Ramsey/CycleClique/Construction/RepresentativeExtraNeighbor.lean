import OAI.Combinatorics.Ramsey.CycleClique.Construction.RepresentativeBallGrowth

namespace OAI

/-! An additional excluded vertex outside the representative set forces
the first ball to exceed the maximum clique size. -/

namespace CycleClique.Construction
open scoped Classical

variable {V : Type} [Fintype V] {G : SimpleGraph V} {X R : Finset V} {x y : V} {k : ℕ}

theorem representative_ball_one_extra (hxR : x ∈ R) (hRX : R ⊆ X) (hXk : X.card ≤ k)
    (hyX : y ∈ X) (hyR : y ∉ R)
    (hexpand : ∀ v, k + 1 ≤ (closedNeighborhood G {v}).card)
    (hforbid : ∀ z ∈ R, x ≠ z → ¬ OutsidePath G (X : Set V) x z 1)
    (hmiss : ∀ u ∈ outsideBallFinset G X x 0, ¬ G.Adj u y) :
    R.card < (outsideBallFinset G X x 1).card := by
  have hxX := hRX hxR
  have hz := outsideBall_initial_growth (A := ∅) hxX (by simp) (by simp)
    (by simp) (hexpand x)
  simp only [Finset.card_empty, Nat.add_zero] at hz
  have hne : (outsideBallFinset G X x 0).Nonempty := by
    apply Finset.card_pos.mp
    omega
  obtain ⟨u, hu⟩ := hne
  have hI : ({u} : Finset V) ⊆ outsideBallFinset G X x 0 := by simpa using hu
  have hAX : R.erase x ⊆ X := fun _ hv => hRX (Finset.mem_of_mem_erase hv)
  have hf : ∀ z ∈ R.erase x, ∀ d, 1 ≤ d → d ≤ 0 + 1 →
      ¬ PositiveOutsidePath G (X : Set V) x z d := by
    intro z hz d hd hdb hp
    have he : d = 1 := by omega
    subst d
    exact hforbid z (Finset.mem_of_mem_erase hz) (Finset.ne_of_mem_erase hz).symm hp.toOutside
  have havoidR := closedNeighborhood_avoids_forbidden hxX hAX (by simp) hI hf
  have havoidy : y ∉ closedNeighborhood G {u} := by
    intro hc
    rcases mem_closedNeighborhood.mp hc with hcu | ⟨v, hv, hvy⟩
    · have he : y = u := Finset.mem_singleton.mp hcu
      exact (mem_outsideBallFinset.mp hu).1 (he ▸ hyX)
    · have he : v = u := Finset.mem_singleton.mp hv
      exact hmiss u hu (he ▸ hvy)
  have hAX' : insert y (R.erase x) ⊆ X := by
    intro z hz
    rcases Finset.mem_insert.mp hz with rfl | hz
    · exact hyX
    · exact hAX hz
  have havoid : ∀ z ∈ insert y (R.erase x), z ∉ closedNeighborhood G {u} := by
    intro z hz
    rcases Finset.mem_insert.mp hz with rfl | hz
    · exact havoidy
    · exact havoidR z hz
  have hg := outsideBall_growth hAX' hI havoid (by simpa using hexpand u)
  have hyErase : y ∉ R.erase x := fun h => hyR (Finset.mem_of_mem_erase h)
  rw [Finset.card_insert_of_notMem hyErase] at hg
  have hc := Finset.card_erase_add_one hxR
  simp only [Finset.card_singleton, Nat.mul_one, Nat.reduceAdd] at hg
  omega

theorem representative_ball_one_not_clique (hxR : x ∈ R) (hRX : R ⊆ X) (hXk : X.card ≤ k)
    (hyX : y ∈ X) (hyR : y ∉ R) (hclique : G.cliqueNum ≤ R.card)
    (hexpand : ∀ v, k + 1 ≤ (closedNeighborhood G {v}).card)
    (hforbid : ∀ z ∈ R, x ≠ z → ¬ OutsidePath G (X : Set V) x z 1)
    (hmiss : ∀ u ∈ outsideBallFinset G X x 0, ¬ G.Adj u y) :
    ¬ G.IsClique (outsideBallFinset G X x 1 : Set V) := by
  intro h
  have hcard := h.card_le_cliqueNum.trans hclique
  have hbig := representative_ball_one_extra hxR hRX hXk hyX hyR hexpand hforbid hmiss
  omega

end CycleClique.Construction

end OAI
