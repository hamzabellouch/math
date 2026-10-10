import OAI.Probability.SwitchChain.PairFiber
import OAI.Probability.SwitchChain.FourVertexSwitch
import OAI.Probability.SwitchChain.SwitchMultiplicity

namespace OAI

noncomputable section

namespace Problem315.PairFiber

theorem fourVertexState_key {n : ℕ} {d : Fin n → ℕ}
    (G : GraphState n d) (i u v j : Fin n) (h : FourDistinct i u v j)
    (hiu : G.val.Adj i u) (hvj : G.val.Adj v j)
    (hiv : ¬ G.val.Adj i v) (huj : ¬ G.val.Adj u j) :
    key i j (fourVertexState G i u v j h).val = key i j G.val := by
  classical
  have hl (w : Fin n) : (fourVertexState G i u v j h).val.Adj i w ↔
      (G.val.Adj i w ∧ w ≠ u) ∨ w = v :=
    proposalResult_fourVertex_adj_first G.val i u v j h hiu hvj hiv huj w
  have hr (w : Fin n) : (fourVertexState G i u v j h).val.Adj j w ↔
      (G.val.Adj j w ∧ w ≠ v) ∨ w = u := by
    simpa [fourVertexState, h.2.2.1.symm, h.2.2.2.2.1.symm, h.2.2.2.2.2.symm] using
      proposalResult_fourVertex_adj G.val i u v j h hiu hvj hiv huj j w
  apply key_eq_of
  · intro x y hx hy
    change (proposalResult G.val (fourVertexProposal i u v j h)).Adj x y ↔ _
    rw [proposalResult_fourVertex_adj G.val i u v j h hiu hvj hiv huj]
    simp [hx.1, hx.2, hy.1, hy.2]
  · rw [hl]
    simp [h.2.2.2.2.1.symm, h.2.2.2.2.2.symm]
  · intro w
    have hju : ¬ G.val.Adj j u := fun hadj => huj hadj.symm
    have hjv : G.val.Adj j v := hvj.symm
    by_cases hwu : w = u
    · subst w
      simp [edgeBit, hl, hr, hiu, hju, h.2.2.2.1]
    by_cases hwv : w = v
    · subst w
      simp [edgeBit, hl, hr, hiv, hjv, h.2.2.2.1.symm]
    simp [edgeBit, hl, hr, hwu, hwv]

theorem fourVertexState_leftSet {n : ℕ} {d : Fin n → ℕ}
    (G : GraphState n d) (i u v j : Fin n) (h : FourDistinct i u v j)
    (hiu : G.val.Adj i u) (hvj : G.val.Adj v j)
    (hiv : ¬ G.val.Adj i v) (huj : ¬ G.val.Adj u j) :
    leftSet (fourVertexState G i u v j h).val i j =
      insert v ((leftSet G.val i j).erase u) := by
  classical
  have hl (w : Fin n) : (fourVertexState G i u v j h).val.Adj i w ↔
      (G.val.Adj i w ∧ w ≠ u) ∨ w = v :=
    proposalResult_fourVertex_adj_first G.val i u v j h hiu hvj hiv huj w
  have hr (w : Fin n) : (fourVertexState G i u v j h).val.Adj j w ↔
      (G.val.Adj j w ∧ w ≠ v) ∨ w = u := by
    simpa [fourVertexState, h.2.2.1.symm, h.2.2.2.2.1.symm, h.2.2.2.2.2.symm] using
      proposalResult_fourVertex_adj G.val i u v j h hiu hvj hiv huj j w
  ext w
  simp only [mem_leftSet, Finset.mem_insert, Finset.mem_erase, hl, hr]
  by_cases hwu : w = u
  · subst w
    simp [h.2.2.2.1]
  by_cases hwv : w = v
  · subst w
    simp [Outside, h.2.1.symm, h.2.2.2.2.2, h.2.2.2.1.symm]
  simp [hwu, hwv, and_comm]

theorem exchange_leftSet_subset {n : ℕ} {d : Fin n → ℕ}
    (G : GraphState n d) (i u v j : Fin n) (h : FourDistinct i u v j)
    (hvj : G.val.Adj v j) (hiv : ¬ G.val.Adj i v) :
    insert v ((leftSet G.val i j).erase u) ⊆ singletonSet G.val i j := by
  classical
  intro w hw
  rcases Finset.mem_insert.mp hw with hw | hw
  · subst w
    exact (mem_singletonSet G.val i j v).mpr
      ⟨⟨h.2.1.symm, h.2.2.2.2.2⟩, Or.inr ⟨hvj.symm, hiv⟩⟩
  · exact leftSet_subset_singletonSet G.val i j (Finset.mem_of_mem_erase hw)

theorem trade_exchange_eq_fourVertexState {n : ℕ} {d : Fin n → ℕ}
    (G : GraphState n d) (i u v j : Fin n) (h : FourDistinct i u v j)
    (hiu : G.val.Adj i u) (hvj : G.val.Adj v j)
    (hiv : ¬ G.val.Adj i v) (huj : ¬ G.val.Adj u j) :
    trade G.val i j h.2.2.1 (insert v ((leftSet G.val i j).erase u))
      (exchange_leftSet_subset G i u v j h hvj hiv) =
        (fourVertexState G i u v j h).val := by
  apply graph_eq_of_key_leftSet_eq
  · exact (key_trade _ _ _ _ _ _).trans
      (fourVertexState_key G i u v j h hiu hvj hiv huj).symm
  · rw [leftSet_trade, fourVertexState_leftSet G i u v j h hiu hvj hiv huj]

theorem switchStep_of_trade_exchange {n : ℕ} {d : Fin n → ℕ}
    (G H : GraphState n d) (i u v j : Fin n) (h : FourDistinct i u v j)
    (hiu : G.val.Adj i u) (hvj : G.val.Adj v j)
    (hiv : ¬ G.val.Adj i v) (huj : ¬ G.val.Adj u j)
    (hH : H.val = trade G.val i j h.2.2.1
      (insert v ((leftSet G.val i j).erase u))
      (exchange_leftSet_subset G i u v j h hvj hiv)) :
    SwitchStep n d G H := by
  have heq : H = fourVertexState G i u v j h := Subtype.ext
    (hH.trans (trade_exchange_eq_fourVertexState G i u v j h hiu hvj hiv huj))
  rw [heq]
  exact switchStep_fourVertexState G i u v j h hiu hvj hiv huj

theorem switchStep_of_key_leftSet_exchange {n : ℕ} {d : Fin n → ℕ}
    (G H : GraphState n d) (i j u v : Fin n) (hij : i ≠ j)
    (hu : u ∈ leftSet G.val i j) (hv : v ∈ singletonSet G.val i j)
    (hvn : v ∉ leftSet G.val i j)
    (hkey : key i j H.val = key i j G.val)
    (hleft : leftSet H.val i j = insert v ((leftSet G.val i j).erase u)) :
    SwitchStep n d G H := by
  classical
  obtain ⟨huo, hiu, hju⟩ := (mem_leftSet G.val i j u).mp hu
  obtain ⟨hvo, hvxor⟩ := (mem_singletonSet G.val i j v).mp hv
  have hvright : G.val.Adj j v ∧ ¬ G.val.Adj i v := by
    rcases hvxor with hvleft | hvright
    · exact False.elim (hvn ((mem_leftSet G.val i j v).mpr ⟨hvo, hvleft⟩))
    · exact hvright
  have huv : u ≠ v := by
    intro heq
    exact hvn (heq ▸ hu)
  have hdist : FourDistinct i u v j :=
    ⟨huo.1.symm, hvo.1.symm, hij, huv, huo.2, hvo.2⟩
  have huj : ¬ G.val.Adj u j := fun he => hju he.symm
  have heq : H = fourVertexState G i u v j hdist := by
    apply Subtype.ext
    apply graph_eq_of_key_leftSet_eq
    · exact hkey.trans
        (fourVertexState_key G i u v j hdist hiu hvright.1.symm hvright.2 huj).symm
    · exact hleft.trans
        (fourVertexState_leftSet G i u v j hdist hiu hvright.1.symm hvright.2 huj).symm
  rw [heq]
  exact switchStep_fourVertexState G i u v j hdist hiu hvright.1.symm hvright.2 huj

theorem map_swap_eq_exchange {V : Type*} [DecidableEq V]
    (A : Finset V) (u v : V) (hu : u ∈ A) (hv : v ∉ A) :
    A.map (Equiv.swap u v).toEmbedding = insert v (A.erase u) := by
  classical
  have huv : u ≠ v := fun heq => hv (heq ▸ hu)
  ext w
  simp only [Finset.mem_map_equiv, Equiv.symm_swap,
    Finset.mem_insert, Finset.mem_erase]
  by_cases hwu : w = u
  · subst w
    simp [huv, hv]
  by_cases hwv : w = v
  · subst w
    simp [hu]
  simp [Equiv.swap_apply_of_ne_of_ne hwu hwv, hwu, hwv]

theorem map_swap_eq_self_of_mem_iff {V : Type*} [DecidableEq V]
    (A : Finset V) (u v : V) (hmem : u ∈ A ↔ v ∈ A) :
    A.map (Equiv.swap u v).toEmbedding = A := by
  classical
  ext w
  simp only [Finset.mem_map_equiv, Equiv.symm_swap]
  by_cases hwu : w = u
  · subst w
    simpa using hmem.symm
  by_cases hwv : w = v
  · subst w
    simpa using hmem
  rw [Equiv.swap_apply_of_ne_of_ne hwu hwv]

theorem eq_or_switchStep_of_key_leftSet_swap {n : ℕ} {d : Fin n → ℕ}
    (G H : GraphState n d) (i j u v : Fin n) (hij : i ≠ j)
    (hu : u ∈ singletonSet G.val i j) (hv : v ∈ singletonSet G.val i j)
    (hkey : key i j H.val = key i j G.val)
    (hleft : leftSet H.val i j =
      (leftSet G.val i j).map (Equiv.swap u v).toEmbedding) :
    G = H ∨ SwitchStep n d G H := by
  classical
  by_cases hul : u ∈ leftSet G.val i j
  · by_cases hvl : v ∈ leftSet G.val i j
    · left
      apply Subtype.ext
      apply graph_eq_of_key_leftSet_eq hkey.symm
      rw [hleft, map_swap_eq_self_of_mem_iff _ u v (by simp [hul, hvl])]
    · right
      exact switchStep_of_key_leftSet_exchange G H i j u v hij hul hv hvl hkey
        (hleft.trans (map_swap_eq_exchange _ u v hul hvl))
  · by_cases hvl : v ∈ leftSet G.val i j
    · right
      apply switchStep_of_key_leftSet_exchange G H i j v u hij hvl hu hul hkey
      rw [hleft, Equiv.swap_comm u v]
      exact map_swap_eq_exchange _ v u hvl hul
    · left
      apply Subtype.ext
      apply graph_eq_of_key_leftSet_eq hkey.symm
      rw [hleft, map_swap_eq_self_of_mem_iff _ u v (by simp [hul, hvl])]

theorem fourVertexProposal_mem_crossingPairs {n : ℕ}
    (i u v j : Fin n) (h : FourDistinct i u v j) :
    ({i, j} : Finset (Fin n)) ∈
      SwitchPairFiber.crossingPairs (fourVertexProposal i u v j h) := by
  classical
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_powersetCard.mpr ⟨?_, ?_⟩, ?_⟩
  · have hs : (fourVertexProposal i u v j h).1.val = {i, u, v, j} := by
      rcases h with ⟨h1, h2, h3, h4, h5, h6⟩
      rfl
    rw [hs]
    intro w hw
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw ⊢
    tauto
  · simp [h.2.2.1]
  · intro x y hxy
    simp only [removedMatching_fourVertexProposal, addedMatching_fourVertexProposal] at hxy
    rcases hxy with (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) |
      (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;>
      simp [h.1.symm, h.2.1.symm, h.2.2.1,
        h.2.2.2.2.1, h.2.2.2.2.2]

theorem exists_crossingProposal_of_key_leftSet_exchange {n : ℕ} {d : Fin n → ℕ}
    (G H : GraphState n d) (i j u v : Fin n) (hij : i ≠ j)
    (hu : u ∈ leftSet G.val i j) (hv : v ∈ singletonSet G.val i j)
    (hvn : v ∉ leftSet G.val i j)
    (hkey : key i j H.val = key i j G.val)
    (hleft : leftSet H.val i j = insert v ((leftSet G.val i j).erase u)) :
    ∃ p : SwitchProposal n, validSwitch G.val p ∧
      ({i, j} : Finset (Fin n)) ∈ SwitchPairFiber.crossingPairs p ∧
      proposalResult G.val p = H.val := by
  classical
  obtain ⟨huo, hiu, hju⟩ := (mem_leftSet G.val i j u).mp hu
  obtain ⟨hvo, hvxor⟩ := (mem_singletonSet G.val i j v).mp hv
  have hvright : G.val.Adj j v ∧ ¬ G.val.Adj i v := by
    rcases hvxor with hvleft | hvright
    · exact False.elim (hvn ((mem_leftSet G.val i j v).mpr ⟨hvo, hvleft⟩))
    · exact hvright
  have huv : u ≠ v := fun heq => hvn (heq ▸ hu)
  have hdist : FourDistinct i u v j :=
    ⟨huo.1.symm, hvo.1.symm, hij, huv, huo.2, hvo.2⟩
  have huj : ¬ G.val.Adj u j := fun he => hju he.symm
  refine ⟨fourVertexProposal i u v j hdist,
    (validSwitch_fourVertexProposal_iff G.val i u v j hdist).mpr
      ⟨hiu, hvright.1.symm, hvright.2, huj⟩,
    fourVertexProposal_mem_crossingPairs i u v j hdist, ?_⟩
  change (fourVertexState G i u v j hdist).val = H.val
  apply graph_eq_of_key_leftSet_eq
  · exact (fourVertexState_key G i u v j hdist hiu hvright.1.symm hvright.2 huj).trans hkey.symm
  · exact (fourVertexState_leftSet G i u v j hdist hiu hvright.1.symm hvright.2 huj).trans hleft.symm

end Problem315.PairFiber

end

end OAI
