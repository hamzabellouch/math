import Mathlib

namespace OAI

namespace CycleClique
open scoped SimpleGraph
attribute [local instance] Classical.propDecidable

structure PathSystem {V : Type*} (G : SimpleGraph V) (Q : Set V) where
  chains : List (List V)
  nonempty : ∀ c ∈ chains, c ≠ []
  nodup : chains.flatten.Nodup
  edges : ∀ c ∈ chains, c.IsChain G.Adj
  positive : ∀ c ∈ chains, c.IsChain (fun u v => u ∉ Q ∨ v ∉ Q)
  ends : ∀ c ∈ chains, (∀ x ∈ c.head?, x ∈ Q) ∧ (∀ x ∈ c.getLast?, x ∈ Q)
  cover : ∀ x ∈ Q, x ∈ chains.flatten

 

theorem clique_chains_flatten {V : Type*} {G : SimpleGraph V} {Q : Set V}
    (hQ : G.IsClique Q) (C : List (List V)) (hne : [] ∉ C)
    (hnd : C.flatten.Nodup) (hedges : ∀ c ∈ C, c.IsChain G.Adj)
    (hends : ∀ c ∈ C, (∀ x ∈ c.head?, x ∈ Q) ∧ (∀ x ∈ c.getLast?, x ∈ Q)) :
    C.flatten.IsChain G.Adj := by
  apply (List.isChain_flatten hne).mpr
  refine ⟨hedges, ?_⟩
  apply List.Pairwise.isChain
  apply (List.nodup_flatten.mp hnd).2.imp_of_mem
  intro a b ha hb hab x hx y hy
  apply hQ ((hends a ha).2 x hx) ((hends b hb).1 y hy)
  intro hxy
  exact List.disjoint_left.mp hab (List.mem_of_mem_getLast? hx)
    (hxy ▸ List.mem_of_mem_head? hy)

theorem clique_chains_endpoints {V : Type*} {Q : Set V} (C : List (List V))
    (hne : ∀ c ∈ C, c ≠ [])
    (hends : ∀ c ∈ C, (∀ x ∈ c.head?, x ∈ Q) ∧ (∀ x ∈ c.getLast?, x ∈ Q))
    (hf : C.flatten ≠ []) :
    C.flatten.head hf ∈ Q ∧ C.flatten.getLast hf ∈ Q := by
  have hc : C ≠ [] := by intro h; simp [h] at hf
  constructor
  · rw [List.head_flatten_eq_head_head hf (hne _ (List.head_mem hc))]
    apply (hends _ (List.head_mem hc)).1
    exact List.head?_eq_some_head (hne _ (List.head_mem hc))
  · rw [List.getLast_flatten_eq_getLast_getLast hf (hne _ (List.getLast_mem hc))]
    apply (hends _ (List.getLast_mem hc)).2
    exact List.getLast?_eq_some_getLast (hne _ (List.getLast_mem hc))

 
theorem close_clique_chains {V : Type*} {G : SimpleGraph V} {Q : Set V}
    (hQ : G.IsClique Q) (C : List (List V))
    (hne : ∀ c ∈ C, c ≠ []) (hnd : C.flatten.Nodup)
    (hedges : ∀ c ∈ C, c.IsChain G.Adj)
    (hends : ∀ c ∈ C, (∀ x ∈ c.head?, x ∈ Q) ∧ (∀ x ∈ c.getLast?, x ∈ Q))
    (hlen : 3 ≤ C.flatten.length) :
    SimpleGraph.cycleGraph C.flatten.length ⊑ G := by
  have hfn : C.flatten ≠ [] := by intro h; simp [h] at hlen
  have hpchain := clique_chains_flatten hQ C (fun hh => hne [] hh rfl) hnd hedges hends
  let p := SimpleGraph.Walk.ofSupport C.flatten hfn hpchain
  have hp : p.IsPath := p.isPath_def.mpr (by simpa [p] using hnd)
  have hplen : p.length = C.flatten.length - 1 := SimpleGraph.Walk.length_ofSupport _ _
  obtain ⟨hx, hy⟩ := clique_chains_endpoints C hne hends hfn
  have hxy : C.flatten.head hfn ≠ C.flatten.getLast hfn := by
    intro heq
    obtain ⟨v, hv⟩ := (List.Nodup.head_eq_getLast_iff hfn hnd).mp heq
    simp [hv] at hlen
  have hadj := hQ hy hx (Ne.symm hxy)
  have hc : (SimpleGraph.Walk.cons hadj p).IsCycle := by
    apply (p.cons_isCycle_iff hadj).mpr
    refine ⟨hp, ?_⟩
    intro he
    have hh := hp.length_eq_one_of_mem_edges (by simpa only [Sym2.eq_swap] using he)
    omega
  apply (SimpleGraph.cycleGraph_isContained_iff (by omega)).mpr
  refine ⟨_, SimpleGraph.Walk.cons hadj p, hc, ?_⟩
  rw [SimpleGraph.Walk.length_cons, hplen]
  omega

theorem flatten_singletons {V : Type*} (l : List V) :
    (l.map (fun v => [v])).flatten = l := by
  induction l with
  | nil => rfl
  | cons x l ih => simp only [List.map_cons, List.flatten_cons, ih, List.singleton_append]

noncomputable def PathSystem.empty {V : Type*} [Fintype V]
    (G : SimpleGraph V) (Q : Set V) : PathSystem G Q := by
  classical
  refine ⟨Q.toFinset.toList.map (fun v => [v]), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro c hc
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hc
    simp
  · rw [flatten_singletons]
    exact Q.toFinset.nodup_toList
  · intro c hc
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hc
    exact .singleton _
  · intro c hc
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hc
    exact .singleton _
  · intro c hc
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hc
    have hvQ : v ∈ Q := by simpa using hv
    simpa using And.intro hvQ hvQ
  · intro x hx
    simpa using hx

noncomputable def PathSystem.amount {V : Type*} [Fintype V]
    {G : SimpleGraph V} {Q : Set V} (P : PathSystem G Q) : ℕ :=
  P.chains.flatten.length - Q.ncard

noncomputable def PathSystem.edgeCount {V : Type*} [Fintype V]
    {G : SimpleGraph V} {Q : Set V} (P : PathSystem G Q) : ℕ :=
  Q.ncard - P.chains.length

noncomputable def PathSystem.singletons {V : Type*}
    {G : SimpleGraph V} {Q : Set V} (P : PathSystem G Q) : List (List V) := by
  classical
  exact P.chains.filter (fun c => c.length = 1)

noncomputable def PathSystem.usedChains {V : Type*}
    {G : SimpleGraph V} {Q : Set V} (P : PathSystem G Q) : List (List V) := by
  classical
  exact P.chains.filter (fun c => c.length ≠ 1)

noncomputable def PathSystem.incident {V : Type*} [Fintype V]
    {G : SimpleGraph V} {Q : Set V} (P : PathSystem G Q) : ℕ :=
  Q.ncard - P.singletons.length

theorem PathSystem.flat_length {V : Type*} [Fintype V]
    {G : SimpleGraph V} {Q : Set V} (P : PathSystem G Q) :
    P.chains.flatten.length = Q.ncard + P.amount := by
  classical
  have h : Q.ncard ≤ P.chains.flatten.length := by
    have hsub : Q ⊆ (P.chains.flatten.toFinset : Set V) := by
      intro x hx
      exact List.mem_toFinset.mpr (P.cover x hx)
    have hh := Set.ncard_le_ncard hsub
    simpa only [Set.ncard_coe_finset, List.toFinset_card_of_nodup P.nodup] using hh
  dsimp [PathSystem.amount]
  omega

theorem PathSystem.clique_count {V : Type*} [Fintype V]
    {G : SimpleGraph V} {Q : Set V} (P : PathSystem G Q) :
    P.chains.flatten.countP (fun x => decide (x ∈ Q)) = Q.ncard := by
  classical
  let l := P.chains.flatten.filter (fun x => decide (x ∈ Q))
  have hnd : l.Nodup := P.nodup.filter _
  have he : (l.toFinset : Set V) = Q := by
    ext x
    simp only [Finset.mem_coe, List.mem_toFinset, l, List.mem_filter, decide_eq_true_eq]
    exact ⟨And.right, fun hx => ⟨P.cover x hx, hx⟩⟩
  have hc := congrArg Set.ncard he
  simpa only [Set.ncard_coe_finset, List.toFinset_card_of_nodup hnd,
    l, ← List.countP_eq_length_filter] using hc

 
theorem no_consecutive_count {V : Type*} (Q : Set V) (c : List V)
    (h : c.IsChain (fun u v => u ∉ Q ∨ v ∉ Q)) :
    2 * c.countP (fun x => decide (x ∈ Q)) ≤
      c.length + if ∃ x ∈ c.head?, x ∈ Q then 1 else 0 := by
  classical
  induction c with
  | nil => simp
  | cons x c ih =>
    have ih := ih h.tail
    by_cases hx : x ∈ Q
    · cases c with
      | nil => simp [hx]
      | cons y c =>
        have hy : y ∉ Q := h.rel.resolve_left (fun hn => hn hx)
        simp [hx, hy] at ih ⊢
        omega
    · simp [hx]
      split_ifs at ih <;> omega

theorem PathSystem.edgeCount_le_amount {V : Type*} [Fintype V]
    {G : SimpleGraph V} {Q : Set V} (P : PathSystem G Q) :
    P.edgeCount ≤ P.amount := by
  classical
  have hb : ∀ c ∈ P.chains,
      2 * c.countP (fun x => decide (x ∈ Q)) ≤ c.length + 1 := by
    intro c hc
    have hh := no_consecutive_count Q c (P.positive c hc)
    split_ifs at hh <;> omega
  have hs := List.sum_le_sum hb
  have he : (P.chains.map (fun c => 2 * c.countP (fun x => decide (x ∈ Q)))).sum =
      2 * P.chains.flatten.countP (fun x => decide (x ∈ Q)) := by
    rw [List.countP_flatten]
    simp only [← List.sum_map_mul_left]
  have he' : (P.chains.map (fun c => c.length + 1)).sum =
      P.chains.flatten.length + P.chains.length := by
    simp [List.sum_map_add, List.length_flatten]
  rw [he, he', P.clique_count, P.flat_length] at hs
  dsimp [PathSystem.edgeCount]
  omega

theorem PathSystem.chains_length_le {V : Type*} [Fintype V]
    {G : SimpleGraph V} {Q : Set V} (P : PathSystem G Q) :
    P.chains.length ≤ Q.ncard := by
  classical
  have hb : ∀ c ∈ P.chains, 1 ≤ c.countP (fun x => decide (x ∈ Q)) := by
    intro c hc
    apply Nat.succ_le_iff.mpr
    apply List.countP_pos_iff.mpr
    let x := c.head (P.nonempty c hc)
    refine ⟨x, List.head_mem _, ?_⟩
    apply decide_eq_true
    exact (P.ends c hc).1 x (List.head?_eq_some_head _)
  have hh := List.sum_le_sum hb
  rw [← List.countP_flatten, P.clique_count] at hh
  simpa using hh

theorem PathSystem.singletons_length_le {V : Type*} [Fintype V]
    {G : SimpleGraph V} {Q : Set V} (P : PathSystem G Q) :
    P.singletons.length ≤ Q.ncard :=
  (List.length_filter_le _ _).trans P.chains_length_le

theorem PathSystem.partition {V : Type*}
    {G : SimpleGraph V} {Q : Set V} (P : PathSystem G Q) :
    (P.usedChains ++ P.singletons).Perm P.chains := by
  classical
  simpa [PathSystem.usedChains, PathSystem.singletons] using
    List.filter_append_perm (fun c : List V => decide (c.length ≠ 1)) P.chains

theorem singletons_flat_length {V : Type*} (C : List (List V))
    (h : ∀ c ∈ C, c.length = 1) : C.flatten.length = C.length := by
  induction C with
  | nil => rfl
  | cons c C ih =>
    rw [List.flatten_cons, List.length_append, h c (by simp),
      ih (fun c hc => h c (by simp [hc])), List.length_cons]
    omega

theorem PathSystem.singleton_flat_length {V : Type*}
    {G : SimpleGraph V} {Q : Set V} (P : PathSystem G Q) :
    P.singletons.flatten.length = P.singletons.length := by
  apply singletons_flat_length
  intro c hc
  exact (List.mem_filter.mp hc).2 |> of_decide_eq_true

theorem PathSystem.closing_interval {V : Type*} [Fintype V]
    {G : SimpleGraph V} {Q : Set V} (P : PathSystem G Q)
    {k : ℕ} (hk : 3 ≤ k) (hQ : G.IsClique Q)
    (hcycle : ¬ SimpleGraph.cycleGraph (k + 1) ⊑ G)
    (ht : Q.ncard ≤ k) (hlo : k + 1 - Q.ncard ≤ P.amount)
    (hhi : P.amount ≤ k + 1 - P.incident) : False := by
  classical
  let u := k + 1 - P.amount - P.incident
  have hi : P.incident ≤ Q.ncard := Nat.sub_le _ _
  have he : P.incident + P.singletons.length = Q.ncard := by
    dsimp [PathSystem.incident]
    have := P.singletons_length_le
    omega
  have hup : u ≤ P.singletons.length := by dsimp [u]; omega
  let C := P.usedChains ++ P.singletons.take u
  have hsub : C.Sublist (P.usedChains ++ P.singletons) :=
    List.Sublist.append (.refl _) (List.take_sublist _ _)
  have hmem : ∀ c ∈ C, c ∈ P.chains := fun c hc => P.partition.subset (hsub.subset hc)
  have hnd : C.flatten.Nodup := hsub.flatten.nodup
    (P.partition.flatten.nodup_iff.mpr P.nodup)
  have hlen₁ := P.partition.flatten.length_eq
  rw [List.flatten_append, List.length_append, P.singleton_flat_length,
    P.flat_length] at hlen₁
  have hlen₂ : (P.singletons.take u).flatten.length = u := by
    rw [singletons_flat_length _ (by
      intro c hc
      exact of_decide_eq_true (List.mem_filter.mp (List.mem_of_mem_take hc)).2),
      List.length_take, Nat.min_eq_left hup]
  have hlen : C.flatten.length = k + 1 := by
    dsimp [C]
    rw [List.flatten_append, List.length_append, hlen₂]
    dsimp [u] at *
    omega
  apply hcycle
  rw [← hlen]
  apply close_clique_chains hQ C (fun c hc => P.nonempty c (hmem c hc)) hnd
    (fun c hc => P.edges c (hmem c hc)) (fun c hc => P.ends c (hmem c hc))
  omega

@[simp] theorem PathSystem.empty_amount {V : Type*} [Fintype V]
    (G : SimpleGraph V) (Q : Set V) : (PathSystem.empty G Q).amount = 0 := by
  classical
  simp [PathSystem.amount, PathSystem.empty, flatten_singletons, Set.ncard_eq_toFinset_card']

end CycleClique

end OAI
