import OAI.Probability.SpanningForest.Definitions

namespace OAI

noncomputable section

open Filter

namespace Problem336

theorem GraphConnected.exists_adj {G : GraphCode} (hG : GraphConnected G) (u : ℕ) :
    ∃ v, Adj G u v := by
  rcases (hG u (u + 1)).cases_head with h | ⟨v, huv, _⟩
  · omega
  · exact ⟨v, huv⟩

namespace IsConnectedExhaustion

variable {G : GraphCode} {H : ℕ → FiniteSubgraphCode}

theorem monotone_vertices (hH : IsConnectedExhaustion G H) :
    Monotone (fun n => (H n).1) :=
  monotone_nat_of_le_succ (fun n => (hH.2.1 n).1)

theorem monotone_edges (hH : IsConnectedExhaustion G H) :
    Monotone (fun n => (H n).2) :=
  monotone_nat_of_le_succ (fun n => (hH.2.1 n).2)

theorem eventually_mem_edges (hH : IsConnectedExhaustion G H)
    (e : EdgeCode) (he : Adj G e.1.1 e.1.2) :
    ∀ᶠ n in atTop, e.1 ∈ (H n).2 := by
  obtain ⟨n, hn⟩ := hH.2.2 e.1.1 e.1.2 e.2 he
  filter_upwards [eventually_ge_atTop n] with m hm
  exact hH.monotone_edges hm hn

theorem eventually_mem_edges_finset (hH : IsConnectedExhaustion G H)
    (s : Finset EdgeCode) (hs : ∀ e ∈ s, Adj G e.1.1 e.1.2) :
    ∀ᶠ n in atTop, ∀ e ∈ s, e.1 ∈ (H n).2 := by
  rw [Finset.eventually_all]
  intro e he
  exact hH.eventually_mem_edges e (hs e he)

theorem endpoints_mem (hH : IsConnectedExhaustion G H)
    {n : ℕ} {p : ℕ × ℕ} (hp : p ∈ (H n).2) :
    p.1 ∈ (H n).1 ∧ p.2 ∈ (H n).1 := by
  exact ⟨((hH.1 n).2.1 p hp).1, ((hH.1 n).2.1 p hp).2.1⟩

theorem eventually_mem_rawPair (hH : IsConnectedExhaustion G H)
    {u v : ℕ} (huv : Adj G u v) :
    ∀ᶠ n in atTop, rawPair u v ∈ (H n).2 := by
  have hne : u ≠ v := by
    intro h
    subst v
    have hfalse := G.2.1 u
    simp [Adj, hfalse] at huv
  unfold rawPair
  split_ifs with hlt
  · exact hH.eventually_mem_edges ⟨(u, v), hlt⟩ huv
  · have hgt : v < u := lt_of_le_of_ne (Nat.le_of_not_gt hlt) (Ne.symm hne)
    have hvu : Adj G v u := by
      unfold Adj at *
      rw [G.2.2 v u]
      exact huv
    exact hH.eventually_mem_edges ⟨(v, u), hgt⟩ hvu

theorem eventually_mem_vertices (hH : IsConnectedExhaustion G H)
    (hG : GraphConnected G) (u : ℕ) :
    ∀ᶠ n in atTop, u ∈ (H n).1 := by
  obtain ⟨v, huv⟩ := hG.exists_adj u
  filter_upwards [hH.eventually_mem_rawPair huv] with n hn
  have hend := hH.endpoints_mem hn
  unfold rawPair at hend
  split_ifs at hend with hlt
  · exact hend.1
  · exact hend.2

theorem eventually_subset_vertices (hH : IsConnectedExhaustion G H)
    (hG : GraphConnected G) (s : Finset ℕ) :
    ∀ᶠ n in atTop, s ⊆ (H n).1 := by
  change ∀ᶠ n in atTop, ∀ u ∈ s, u ∈ (H n).1
  rw [Finset.eventually_all]
  intro u _
  exact hH.eventually_mem_vertices hG u

theorem eventually_subset_edges (hH : IsConnectedExhaustion G H)
    (s : Finset (ℕ × ℕ))
    (hs : ∀ p ∈ s, p.1 < p.2 ∧ Adj G p.1 p.2) :
    ∀ᶠ n in atTop, s ⊆ (H n).2 := by
  change ∀ᶠ n in atTop, ∀ p ∈ s, p ∈ (H n).2
  rw [Finset.eventually_all]
  intro p hp
  exact hH.eventually_mem_edges ⟨p, (hs p hp).1⟩ (hs p hp).2

theorem eventually_contains (hH : IsConnectedExhaustion G H)
    (hG : GraphConnected G) {K : FiniteSubgraphCode}
    (hK : IsFiniteConnectedSubgraph G K) :
    ∀ᶠ n in atTop, K.1 ⊆ (H n).1 ∧ K.2 ⊆ (H n).2 := by
  refine (hH.eventually_subset_vertices hG K.1).and ?_
  apply hH.eventually_subset_edges K.2
  intro p hp
  exact ((hK.2.1 p hp).2.2)

end IsConnectedExhaustion

end Problem336

end

end OAI
