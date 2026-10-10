import OAI.Combinatorics.TreewidthL1.Model

namespace OAI

namespace BoundedTreewidthL1

section WeightedPaths

variable {V : Type*} (G : SimpleGraph V) (ℓ : G.edgeSet → ℝ)

/-- Extension by zero, only used to write the sum over `Walk.edges`.
It does not add edges or change any graph-walk length. -/
noncomputable def edgeLength (e : Sym2 V) : ℝ := by
  classical
  exact if h : e ∈ G.edgeSet then ℓ ⟨e, h⟩ else 0

lemma edgeLength_of_mem {e : Sym2 V} (h : e ∈ G.edgeSet) :
    edgeLength G ℓ e = ℓ ⟨e, h⟩ := by
  simp [edgeLength, h]

lemma edgeLength_nonneg (hℓ : ∀ e, 0 ≤ ℓ e) (e : Sym2 V) :
    0 ≤ edgeLength G ℓ e := by
  unfold edgeLength
  split_ifs with h
  · exact hℓ _
  · exact le_rfl

lemma walkLength_eq_sum_edges {u v : V} (p : G.Walk u v) :
    walkLength G ℓ p = (p.edges.map (edgeLength G ℓ)).sum := by
  induction p with
  | nil => rfl
  | @cons u v w h p ih =>
    simp only [walkLength, SimpleGraph.Walk.edges_cons, List.map_cons, List.sum_cons, ih]
    rw [edgeLength_of_mem G ℓ (e := s(u, v)) h]

lemma walkLength_nonneg (hℓ : ∀ e, 0 ≤ ℓ e) {u v : V} (p : G.Walk u v) :
    0 ≤ walkLength G ℓ p := by
  induction p with
  | nil => exact le_rfl
  | cons h p ih => exact add_nonneg (hℓ _) ih

lemma walkLength_pos (hℓ : ∀ e, 0 < ℓ e) {u v : V}
    (huv : u ≠ v) (p : G.Walk u v) : 0 < walkLength G ℓ p := by
  cases p with
  | nil => exact (huv rfl).elim
  | cons h p =>
    exact add_pos_of_pos_of_nonneg (hℓ _) (walkLength_nonneg G ℓ (fun e => (hℓ e).le) p)

lemma walkLength_append {u v w : V} (p : G.Walk u v) (q : G.Walk v w) :
    walkLength G ℓ (p.append q) = walkLength G ℓ p + walkLength G ℓ q := by
  simp only [walkLength_eq_sum_edges, SimpleGraph.Walk.edges_append,
    List.map_append, List.sum_append]

lemma walkLength_reverse {u v : V} (p : G.Walk u v) :
    walkLength G ℓ p.reverse = walkLength G ℓ p := by
  simp [walkLength_eq_sum_edges, SimpleGraph.Walk.edges_reverse]

lemma walkLength_bypass_le [DecidableEq V] (hℓ : ∀ e, 0 ≤ ℓ e)
    {u v : V} (p : G.Walk u v) : walkLength G ℓ p.bypass ≤ walkLength G ℓ p := by
  rw [walkLength_eq_sum_edges, walkLength_eq_sum_edges]
  apply (p.edges_bypass_sublist_edges.map (edgeLength G ℓ)).sum_le_sum
  intro a ha
  obtain ⟨e, _, rfl⟩ := List.mem_map.mp ha
  exact edgeLength_nonneg G ℓ hℓ e

lemma path_length_set_finite [Fintype V] (u v : V) :
    {r : ℝ | ∃ p : G.Walk u v, p.IsPath ∧ walkLength G ℓ p = r}.Finite := by
  classical
  convert Set.finite_range (fun p : G.Path u v => walkLength G ℓ p.val) using 1
  ext r
  constructor
  · rintro ⟨p, hp, hr⟩
    exact ⟨⟨p, hp⟩, hr⟩
  · rintro ⟨p, hr⟩
    exact ⟨p.val, p.property, hr⟩

lemma path_length_set_nonempty (hG : G.Connected) (u v : V) :
    {r : ℝ | ∃ p : G.Walk u v, p.IsPath ∧ walkLength G ℓ p = r}.Nonempty := by
  obtain ⟨p, hp, _⟩ := hG.exists_path_of_dist u v
  exact ⟨walkLength G ℓ p, p, hp, rfl⟩

lemma shortestPathDistance_attained [Fintype V] (hG : G.Connected) (u v : V) :
    ∃ p : G.Walk u v, p.IsPath ∧ walkLength G ℓ p = shortestPathDistance G ℓ u v :=
  (path_length_set_nonempty G ℓ hG u v).csInf_mem (path_length_set_finite G ℓ u v)

lemma shortestPathDistance_nonneg (hG : G.Connected) (hℓ : ∀ e, 0 ≤ ℓ e)
    (u v : V) : 0 ≤ shortestPathDistance G ℓ u v := by
  apply le_csInf (path_length_set_nonempty G ℓ hG u v)
  rintro r ⟨p, _, rfl⟩
  exact walkLength_nonneg G ℓ hℓ p

lemma shortestPathDistance_le_pathLength (hℓ : ∀ e, 0 ≤ ℓ e)
    {u v : V} (p : G.Walk u v) (hp : p.IsPath) :
    shortestPathDistance G ℓ u v ≤ walkLength G ℓ p := by
  unfold shortestPathDistance
  refine csInf_le ?_ ⟨p, hp, rfl⟩
  refine ⟨0, ?_⟩
  rintro r ⟨q, _, rfl⟩
  exact walkLength_nonneg G ℓ hℓ q

lemma shortestPathDistance_le_walkLength (hℓ : ∀ e, 0 ≤ ℓ e)
    {u v : V} (p : G.Walk u v) :
    shortestPathDistance G ℓ u v ≤ walkLength G ℓ p := by
  classical
  exact (shortestPathDistance_le_pathLength G ℓ hℓ p.bypass p.bypass_isPath).trans
    (walkLength_bypass_le G ℓ hℓ p)

lemma shortestPathDistance_self (hG : G.Connected) (hℓ : ∀ e, 0 ≤ ℓ e)
    (u : V) : shortestPathDistance G ℓ u u = 0 :=
  le_antisymm (shortestPathDistance_le_walkLength G ℓ hℓ .nil)
    (shortestPathDistance_nonneg G ℓ hG hℓ u u)

lemma shortestPathDistance_pos [Fintype V] (hG : G.Connected) (hℓ : ∀ e, 0 < ℓ e)
    {u v : V} (huv : u ≠ v) : 0 < shortestPathDistance G ℓ u v := by
  obtain ⟨p, _, hp⟩ := shortestPathDistance_attained G ℓ hG u v
  rw [← hp]
  exact walkLength_pos G ℓ hℓ huv p

lemma shortestPathDistance_comm [Fintype V] (hG : G.Connected) (hℓ : ∀ e, 0 ≤ ℓ e)
    (u v : V) : shortestPathDistance G ℓ u v = shortestPathDistance G ℓ v u := by
  have hd (a b : V) : shortestPathDistance G ℓ a b ≤ shortestPathDistance G ℓ b a := by
    obtain ⟨p, hp, heq⟩ := shortestPathDistance_attained G ℓ hG b a
    rw [← heq, ← walkLength_reverse G ℓ p]
    exact shortestPathDistance_le_pathLength G ℓ hℓ p.reverse hp.reverse
  exact le_antisymm (hd u v) (hd v u)

lemma shortestPathDistance_triangle [Fintype V] (hG : G.Connected) (hℓ : ∀ e, 0 ≤ ℓ e)
    (u v w : V) : shortestPathDistance G ℓ u w ≤
      shortestPathDistance G ℓ u v + shortestPathDistance G ℓ v w := by
  obtain ⟨p, _, hp⟩ := shortestPathDistance_attained G ℓ hG u v
  obtain ⟨q, _, hq⟩ := shortestPathDistance_attained G ℓ hG v w
  rw [← hp, ← hq, ← walkLength_append G ℓ p q]
  exact shortestPathDistance_le_walkLength G ℓ hℓ (p.append q)

theorem shortestPathDistance_metric [Fintype V] (hG : G.Connected)
    (hℓ : ∀ e, 0 < ℓ e) :
    (∀ u v, 0 ≤ shortestPathDistance G ℓ u v) ∧
    (∀ u, shortestPathDistance G ℓ u u = 0) ∧
    (∀ u v, shortestPathDistance G ℓ u v = shortestPathDistance G ℓ v u) ∧
    (∀ u v w, shortestPathDistance G ℓ u w ≤
      shortestPathDistance G ℓ u v + shortestPathDistance G ℓ v w) ∧
    (∀ u v, shortestPathDistance G ℓ u v = 0 → u = v) ∧
    (∀ u v, ∃ p : G.Walk u v,
      p.IsPath ∧ walkLength G ℓ p = shortestPathDistance G ℓ u v) := by
  have hnonneg : ∀ e, 0 ≤ ℓ e := fun e => (hℓ e).le
  refine ⟨shortestPathDistance_nonneg G ℓ hG hnonneg,
    shortestPathDistance_self G ℓ hG hnonneg,
    shortestPathDistance_comm G ℓ hG hnonneg,
    shortestPathDistance_triangle G ℓ hG hnonneg, ?_,
    shortestPathDistance_attained G ℓ hG⟩
  intro u v hzero
  by_contra huv
  have hpos := shortestPathDistance_pos G ℓ hG hℓ huv
  linarith

end WeightedPaths

end BoundedTreewidthL1

end OAI
