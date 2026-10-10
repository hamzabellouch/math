import OAI.Combinatorics.Ramsey.CycleClique.Construction.BallGrowth
import OAI.Combinatorics.Ramsey.CycleClique.Construction.RamseyReduction
import OAI.Combinatorics.Ramsey.CycleClique.Construction.Size

namespace OAI

/-! The independent-pair bounds, including the equality exception, used
by manuscript Lemma `finite:ball-bounds`. -/

namespace CycleClique.Construction
variable {V : Type*} [Fintype V] {G : SimpleGraph V}

omit [Fintype V] in
theorem independent_pair_of_not_clique {Y : Finset V}
    (hY : ¬ G.IsClique (Y : Set V)) : HasIndependent (G.induce (Y : Set V)) 2 := by
  by_contra hn
  apply hY
  intro x hx y hy hxy
  by_contra hadj
  exact hn (independent_pair (x := ⟨x, hx⟩) (y := ⟨y, hy⟩)
    (fun h => hxy (congrArg Subtype.val h)) hadj)

theorem independent_pair_of_card_gt_cliqueNum {Y : Finset V} {t : ℕ}
    (ht : G.cliqueNum ≤ t) (hcard : t < Y.card) :
    HasIndependent (G.induce (Y : Set V)) 2 := by
  apply independent_pair_of_not_clique
  intro h
  have := h.card_le_cliqueNum
  omega

/-- At radius zero, equality with the maximum clique size already
forces a pair, because every vertex of the ball sees its base. -/
theorem outsideBall_initial_pair {X : Finset V} {x : V} {t : ℕ}
    (hx : x ∈ X) (ht : G.cliqueNum ≤ t)
    (hcard : t ≤ (outsideBallFinset G X x 0).card) :
    HasIndependent (G.induce (outsideBallFinset G X x 0 : Set V)) 2 := by
  classical
  apply independent_pair_of_not_clique
  intro hclique
  have hxout : x ∉ outsideBallFinset G X x 0 := by
    intro h
    exact (mem_outsideBallFinset.mp h).1 hx
  have hjoin : G.IsClique ((insert x (outsideBallFinset G X x 0) : Finset V) : Set V) := by
    rw [Finset.coe_insert]
    apply hclique.insert
    intro v hv _
    exact ((outsideBall_zero hx).mp (mem_outsideBallFinset.mp hv)).1
  have hb := hjoin.card_le_cliqueNum.trans ht
  rw [Finset.card_insert_of_notMem hxout] at hb
  omega

/-- The equality exception does not need any extra Hamiltonicity input.
If two successive balls could be the same maximum clique, singleton
expansion would force every vertex of that clique to see its base. -/
theorem outsideBall_exception_pair {X A : Finset V} {x : V} {r k t : ℕ}
    (hx : x ∈ X) (hAX : A ⊆ X) (hxA : x ∉ A)
    (ht : G.cliqueNum ≤ t)
    (hprev : t ≤ (outsideBallFinset G X x r).card)
    (hnum : X.card + t ≤ k + 1 + A.card)
    (hexpand : ∀ v, k + 1 ≤ (closedNeighborhood G {v}).card)
    (hforbid : ∀ y ∈ A, ∀ d, 1 ≤ d → d ≤ r + 1 →
      ¬ PositiveOutsidePath G (X : Set V) x y d) :
    HasIndependent (G.induce (outsideBallFinset G X x (r + 1) : Set V)) 2 := by
  classical
  apply independent_pair_of_not_clique
  intro hclique
  let B := outsideBallFinset G X x r
  let C := outsideBallFinset G X x (r + 1)
  have hBC : B ⊆ C := outsideBallFinset_mono (Nat.le_succ r)
  have hCcard : C.card ≤ t := hclique.card_le_cliqueNum.trans ht
  have heq : B = C := Finset.eq_of_subset_of_card_le hBC (by
    change t ≤ B.card at hprev
    omega)
  have hCC : C.card = t := by
    have := Finset.card_le_card hBC
    change t ≤ B.card at hprev
    omega
  have hxC : x ∉ C := by
    intro h
    exact (mem_outsideBallFinset.mp h).1 hx
  have hxD : x ∈ X \ A := Finset.mem_sdiff.mpr ⟨hx, hxA⟩
  have hDpos : 0 < (X \ A).card := Finset.card_pos.mpr ⟨x, hxD⟩
  have hdcard := Finset.card_sdiff_add_card_eq_card hAX
  have herase := Finset.card_erase_of_mem hxD
  have hjoin : ∀ v ∈ C, G.Adj x v := by
    intro v hv
    have hvB : v ∈ B := heq.symm ▸ hv
    by_contra hnon
    have hsub : closedNeighborhood G {v} ⊆ C ∪ ((X \ A).erase x) := by
      intro w hw
      rcases mem_closedNeighborhood.mp hw with hwv | ⟨u, hu, huw⟩
      · have : w = v := Finset.mem_singleton.mp hwv
        exact Finset.mem_union_left _ (this ▸ hv)
      · have hueq : u = v := Finset.mem_singleton.mp hu
        subst u
        by_cases hwX : w ∈ X
        · apply Finset.mem_union_right
          apply Finset.mem_erase.mpr
          refine ⟨?_, Finset.mem_sdiff.mpr ⟨hwX, ?_⟩⟩
          · intro he
            subst w
            exact hnon huw.symm
          · intro hwA
            exact singleton_outside_ball_separated hx (hAX hwA)
              (fun he => hxA (he ▸ hwA)) (hforbid w hwA) v
              (mem_outsideBallFinset.mp hvB) huw
        · apply Finset.mem_union_left
          exact mem_outsideBallFinset.mpr
            (outsideBall_step (mem_outsideBallFinset.mp hvB) hwX huw)
    have hc := Finset.card_le_card hsub
    have hu := Finset.card_union_le C ((X \ A).erase x)
    have he := hexpand v
    omega
  have hbig : G.IsClique ((insert x C : Finset V) : Set V) := by
    rw [Finset.coe_insert]
    exact hclique.insert (fun v hv _ => hjoin v hv)
  have hc := hbig.card_le_cliqueNum.trans ht
  rw [Finset.card_insert_of_notMem hxC, hCC] at hc
  omega

end CycleClique.Construction

end OAI
