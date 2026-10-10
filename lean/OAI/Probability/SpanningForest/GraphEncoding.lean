import OAI.Probability.SpanningForest.Definitions

namespace OAI

noncomputable section
namespace Problem336
namespace FiniteEncoding

lemma rawPair_comm (u v : ℕ) : rawPair u v = rawPair v u := by
  unfold rawPair
  split_ifs <;> simp_all <;> omega

def graph (K : FiniteSubgraphCode) : SimpleGraph {v : ℕ // v ∈ K.1} where
  Adj u v := u ≠ v ∧ rawPair u.1 v.1 ∈ K.2
  symm := ⟨by
    intro u v h
    exact ⟨h.1.symm, by simpa [rawPair_comm] using h.2⟩⟩
  loopless := ⟨by
    intro u h
    exact h.1 rfl⟩

lemma rawPair_self (u : ℕ) : rawPair u u = (u,u) := by simp [rawPair]

lemma rawPair_ne_of_mem {G : GraphCode} {K : FiniteSubgraphCode}
    (hK : IsFiniteConnectedSubgraph G K) {u v : ℕ}
    (h : rawPair u v ∈ K.2) : u ≠ v := by
  intro huv
  subst v
  have hp := (hK.2.1 _ h).2.2.1
  simp [rawPair_self] at hp

lemma reachable_of_subgraphPath {G : GraphCode} {K : FiniteSubgraphCode}
    (hK : IsFiniteConnectedSubgraph G K) {u v : ℕ}
    (p : Relation.ReflTransGen (SubgraphAdj K) u v)
    (hu : u ∈ K.1) (hv : v ∈ K.1) :
    (graph K).Reachable ⟨u, hu⟩ ⟨v, hv⟩ := by
  induction p with
  | refl => exact SimpleGraph.Reachable.refl _
  | @tail w z p hwz ih =>
    exact (ih hwz.1).trans (SimpleGraph.Adj.reachable (G := graph K)
      ⟨by intro he; exact rawPair_ne_of_mem hK hwz.2.2 (congrArg Subtype.val he), hwz.2.2⟩)

lemma connected {G : GraphCode} {K : FiniteSubgraphCode}
    (hK : IsFiniteConnectedSubgraph G K) : (graph K).Connected := by
  obtain ⟨u, hu⟩ := hK.1
  let : Nonempty {v : ℕ // v ∈ K.1} := ⟨⟨u, hu⟩⟩
  exact ⟨fun v w => reachable_of_subgraphPath hK
    (hK.2.2 v.1 v.2 w.1 w.2) v.2 w.2⟩

def edgePair {s : Finset ℕ} : Sym2 {v : ℕ // v ∈ s} → ℕ × ℕ :=
  Sym2.lift ⟨fun u v => rawPair u.1 v.1, fun u v => rawPair_comm u.1 v.1⟩

@[simp] lemma edgePair_mk {s : Finset ℕ} (u v : {v : ℕ // v ∈ s}) :
    edgePair s(u,v) = rawPair u.1 v.1 := rfl

lemma edgePair_forget {s : Finset ℕ} (e : Sym2 {v : ℕ // v ∈ s}) :
    s((edgePair e).1, (edgePair e).2) = Sym2.map Subtype.val e := by
  induction e using Sym2.inductionOn with
  | _ u v =>
    simp only [edgePair_mk, Sym2.map_mk]
    unfold rawPair
    split_ifs
    · rfl
    · exact Sym2.eq_swap

lemma edgePair_injective {s : Finset ℕ} :
    Function.Injective (edgePair (s := s)) := by
  intro a b hab
  apply Sym2.map.injective Subtype.val_injective
  rw [← edgePair_forget a, ← edgePair_forget b, hab]

def edgePairs {s : Finset ℕ} (F : SimpleGraph {v : ℕ // v ∈ s}) :
    Finset (ℕ × ℕ) := by
  classical
  exact F.edgeFinset.image edgePair

lemma card_edgePairs {s : Finset ℕ} (F : SimpleGraph {v : ℕ // v ∈ s}) :
    (edgePairs F).card = Nat.card F.edgeSet := by
  classical
  rw [edgePairs, Finset.card_image_of_injective _ edgePair_injective,
    SimpleGraph.edgeFinset, Set.toFinset_card, Nat.card_eq_fintype_card]

lemma rawPair_mem_edgePairs {s : Finset ℕ} {F : SimpleGraph {v : ℕ // v ∈ s}}
    {u v : {v : ℕ // v ∈ s}} (h : F.Adj u v) :
    rawPair u.1 v.1 ∈ edgePairs F := by
  classical
  exact Finset.mem_image.mpr ⟨s(u,v), by simpa using h, rfl⟩

lemma edgePairs_subset {K : FiniteSubgraphCode}
    {F : SimpleGraph {v : ℕ // v ∈ K.1}} (hF : F ≤ graph K) :
    edgePairs F ⊆ K.2 := by
  classical
  intro p hp
  obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hp
  induction e using Sym2.inductionOn with
  | _ u v =>
    have h : F.Adj u v := by simpa using he
    exact (hF h).2

lemma treeOn_edgePairs {K : FiniteSubgraphCode}
    {F : SimpleGraph {v : ℕ // v ∈ K.1}}
    (hF : F ≤ graph K) (hT : F.IsTree) : TreeOn K (edgePairs F) := by
  classical
  refine ⟨edgePairs_subset hF, ?_, ?_⟩
  · rw [card_edgePairs]
    simpa [SimpleGraph.edgeFinset, Nat.card_eq_fintype_card] using hT.card_edgeFinset
  · intro u hu v hv
    have hp := (F.reachable_iff_reflTransGen _ _).mp
      (hT.connected ⟨u, hu⟩ ⟨v,hv⟩)
    exact hp.lift Subtype.val (fun a b hab => rawPair_mem_edgePairs hab)

lemma rawPair_mem_endpoints {G : GraphCode} {K : FiniteSubgraphCode}
    (hK : IsFiniteConnectedSubgraph G K) {u v : ℕ}
    (h : rawPair u v ∈ K.2) : u ∈ K.1 ∧ v ∈ K.1 := by
  have hp := hK.2.1 _ h
  unfold rawPair at hp
  split_ifs at hp with huv
  · exact ⟨hp.1, hp.2.1⟩
  · exact ⟨hp.2.1, hp.1⟩

lemma edgePairs_graph {G : GraphCode} {K : FiniteSubgraphCode}
    (hK : IsFiniteConnectedSubgraph G K) : edgePairs (graph K) = K.2 := by
  classical
  apply Finset.Subset.antisymm (edgePairs_subset le_rfl)
  intro p hp
  obtain ⟨hu, hv, huv, _⟩ := hK.2.1 p hp
  have hadj : (graph K).Adj ⟨p.1,hu⟩ ⟨p.2,hv⟩ := by
    refine ⟨?_, ?_⟩
    · intro h
      exact Nat.ne_of_lt huv (congrArg Subtype.val h)
    · simpa [rawPair, huv] using hp
  simpa [rawPair, huv] using rawPair_mem_edgePairs hadj

lemma finiteConnected_treeCode {G : GraphCode} {K : FiniteSubgraphCode}
    (hK : IsFiniteConnectedSubgraph G K) {T : Finset (ℕ × ℕ)}
    (hT : TreeOn K T) : IsFiniteConnectedSubgraph G (K.1,T) := by
  refine ⟨hK.1, ?_, ?_⟩
  · intro p hp
    exact hK.2.1 p (hT.1 hp)
  · intro u hu v hv
    have hrel : TreeAdj T ≤ SubgraphAdj (K.1,T) := by
      intro a b hab
      have hm := rawPair_mem_endpoints hK (hT.1 hab)
      exact ⟨hm.1, hm.2, hab⟩
    exact Relation.ReflTransGen.mono hrel _ _ (hT.2.2 u hu v hv)

lemma isTree_graph_treeCode {G : GraphCode} {K : FiniteSubgraphCode}
    (hK : IsFiniteConnectedSubgraph G K) {T : Finset (ℕ × ℕ)}
    (hT : TreeOn K T) : (graph (K.1,T)).IsTree := by
  have hc := finiteConnected_treeCode hK hT
  apply SimpleGraph.isTree_iff_connected_and_card.mpr
  refine ⟨connected hc, ?_⟩
  rw [← card_edgePairs, edgePairs_graph hc]
  simpa [Nat.card_eq_fintype_card] using hT.2.1

lemma rawPair_mem_edgePairs_iff {s : Finset ℕ}
    {F : SimpleGraph {v : ℕ // v ∈ s}} {u v : {v : ℕ // v ∈ s}} :
    rawPair u.1 v.1 ∈ edgePairs F ↔ F.Adj u v := by
  classical
  constructor
  · intro h
    obtain ⟨e, he, heq⟩ := Finset.mem_image.mp h
    have heq' : e = s(u,v) := edgePair_injective heq
    subst e
    simpa using he
  · exact rawPair_mem_edgePairs

lemma graph_edgePairs {s : Finset ℕ} (F : SimpleGraph {v : ℕ // v ∈ s}) :
    graph (s, edgePairs F) = F := by
  ext u v
  change (u ≠ v ∧ rawPair u.1 v.1 ∈ edgePairs F) ↔ F.Adj u v
  rw [rawPair_mem_edgePairs_iff]
  exact ⟨And.right, fun h => ⟨h.ne, h⟩⟩

lemma edgePairs_graph_of_valid {K : FiniteSubgraphCode}
    (hK : ∀ p ∈ K.2, p.1 ∈ K.1 ∧ p.2 ∈ K.1 ∧ p.1 < p.2) :
    edgePairs (graph K) = K.2 := by
  classical
  apply Finset.Subset.antisymm (edgePairs_subset le_rfl)
  intro p hp
  obtain ⟨hu, hv, huv⟩ := hK p hp
  have hadj : (graph K).Adj ⟨p.1,hu⟩ ⟨p.2,hv⟩ := by
    refine ⟨?_, ?_⟩
    · intro h
      exact Nat.ne_of_lt huv (congrArg Subtype.val h)
    · simpa [rawPair, huv] using hp
  simpa [rawPair, huv] using rawPair_mem_edgePairs hadj

lemma treeOn_iff_isTree {G : GraphCode} {K : FiniteSubgraphCode}
    (hK : IsFiniteConnectedSubgraph G K) {T : Finset (ℕ × ℕ)}
    (hsub : T ⊆ K.2) : TreeOn K T ↔ (graph (K.1,T)).IsTree := by
  constructor
  · exact isTree_graph_treeCode hK
  · intro hT
    have hle : graph (K.1,T) ≤ graph K := by
      intro u v h
      exact ⟨h.1, hsub h.2⟩
    have hvalid : ∀ p ∈ T, p.1 ∈ K.1 ∧ p.2 ∈ K.1 ∧ p.1 < p.2 := by
      intro p hp
      have h := hK.2.1 p (hsub hp)
      exact ⟨h.1, h.2.1, h.2.2.1⟩
    have h := treeOn_edgePairs (K := K) hle hT
    rw [edgePairs_graph_of_valid (K := (K.1,T)) hvalid] at h
    exact h

lemma mem_spanningTrees_iff {K : FiniteSubgraphCode} {T : Finset (ℕ × ℕ)} :
    T ∈ spanningTrees K ↔ TreeOn K T := by
  classical
  simp only [spanningTrees, Finset.mem_filter, Finset.mem_powerset]
  exact ⟨And.right, fun h => ⟨h.1,h⟩⟩

def spanningTreeEquiv {G : GraphCode} {K : FiniteSubgraphCode}
    (hK : IsFiniteConnectedSubgraph G K) :
    {T : Finset (ℕ × ℕ) // T ∈ spanningTrees K} ≃
      {F : SimpleGraph {v : ℕ // v ∈ K.1} // F ≤ graph K ∧ F.IsTree} where
  toFun T := by
    have ht := mem_spanningTrees_iff.mp T.2
    refine ⟨graph (K.1,T.1), ?_, isTree_graph_treeCode hK ht⟩
    intro u v h
    exact ⟨h.1, ht.1 h.2⟩
  invFun F := ⟨edgePairs F.1, mem_spanningTrees_iff.mpr (treeOn_edgePairs F.2.1 F.2.2)⟩
  left_inv T := by
    apply Subtype.ext
    apply edgePairs_graph_of_valid (K := (K.1,T.1))
    intro p hp
    have h := hK.2.1 p ((mem_spanningTrees_iff.mp T.2).1 hp)
    exact ⟨h.1, h.2.1, h.2.2.1⟩
  right_inv F := by
    apply Subtype.ext
    exact graph_edgePairs F.1

lemma card_spanningTrees {G : GraphCode} {K : FiniteSubgraphCode}
    (hK : IsFiniteConnectedSubgraph G K) :
    (spanningTrees K).card =
      Nat.card {F : SimpleGraph {v : ℕ // v ∈ K.1} // F ≤ graph K ∧ F.IsTree} := by
  rw [← Nat.card_congr (spanningTreeEquiv hK), Nat.card_eq_fintype_card, Fintype.card_coe]

lemma spanningTrees_nonempty {G : GraphCode} {K : FiniteSubgraphCode}
    (hK : IsFiniteConnectedSubgraph G K) : (spanningTrees K).Nonempty := by
  obtain ⟨F, hF, hT⟩ := (connected hK).exists_isTree_le
  exact ⟨edgePairs F, mem_spanningTrees_iff.mpr (treeOn_edgePairs hF hT)⟩

end FiniteEncoding
end Problem336

end

end OAI
