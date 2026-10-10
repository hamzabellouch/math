import OAI.Combinatorics.Ramsey.CycleClique.Construction.DistanceLayers

namespace OAI

/-! A coherent choice of predecessors on shortest paths to a root. -/

namespace CycleClique.Construction
theorem exists_distance_predecessor {V : Type*} {G : SimpleGraph V} {root v : V}
    (hr : G.Reachable root v) (hd : 0 < G.dist root v) :
    ∃ w, G.Adj v w ∧ G.dist root w + 1 = G.dist root v ∧ G.Reachable root w := by
  obtain ⟨p, hp⟩ := hr.symm.exists_walk_length_eq_dist
  rw [SimpleGraph.dist_comm] at hp
  cases p with
  | nil => simp only [SimpleGraph.Walk.length_nil] at hp; omega
  | @cons v w root hvw p =>
    have hlen : p.length + 1 = G.dist root v := by simpa using hp
    have hupper : G.dist root w ≤ p.length := by simpa using G.dist_le p.reverse
    have hdiff := hvw.diff_dist_adj (u := root)
    exact ⟨w, hvw, by omega, p.reachable.symm⟩

noncomputable def bfsParent {V : Type*} (G : SimpleGraph V) (root v : V) : V := by
  classical
  exact if h : G.Reachable root v ∧ 0 < G.dist root v then
    Classical.choose (exists_distance_predecessor h.1 h.2) else v

theorem bfsParent_spec {V : Type*} {G : SimpleGraph V} {root v : V}
    (hr : G.Reachable root v) (hd : 0 < G.dist root v) :
    G.Adj v (bfsParent G root v) ∧
      G.dist root (bfsParent G root v) + 1 = G.dist root v ∧
      G.Reachable root (bfsParent G root v) := by
  rw [bfsParent, dite_eq_left ⟨hr, hd⟩]
  exact Classical.choose_spec (exists_distance_predecessor hr hd)

@[simp] theorem bfsParent_root {V : Type*} (G : SimpleGraph V) (root : V) :
    bfsParent G root root = root := by classical exact (by simp [bfsParent])

theorem bfsAncestor_level {V : Type*} {G : SimpleGraph V} {root v : V}
    (hr : G.Reachable root v) :
    ∀ j ≤ G.dist root v,
      G.Reachable root ((bfsParent G root)^[j] v) ∧
      G.dist root ((bfsParent G root)^[j] v) = G.dist root v - j := by
  intro j
  induction j with
  | zero => intro _; simpa using hr
  | succ j ih =>
    intro hj
    obtain ⟨hrj, hdj⟩ := ih (by omega)
    have hpos : 0 < G.dist root ((bfsParent G root)^[j] v) := by omega
    obtain ⟨_, hdnext, hrnext⟩ := bfsParent_spec hrj hpos
    rw [Function.iterate_succ_apply']
    exact ⟨hrnext, by omega⟩

theorem bfsAncestor_root {V : Type*} {G : SimpleGraph V} {root v : V}
    (hr : G.Reachable root v) :
    (bfsParent G root)^[G.dist root v] v = root := by
  obtain ⟨hr', hd⟩ := bfsAncestor_level hr (G.dist root v) le_rfl
  have hz : G.dist root ((bfsParent G root)^[G.dist root v] v) = 0 := by omega
  rcases G.dist_eq_zero_iff_eq_or_not_reachable.mp hz with heq | hn
  · exact heq.symm
  · exact False.elim (hn hr')

theorem bfsAncestor_adjacent {V : Type*} {G : SimpleGraph V} {root v : V}
    (hr : G.Reachable root v) {j : ℕ} (hj : j < G.dist root v) :
    G.Adj ((bfsParent G root)^[j] v) ((bfsParent G root)^[j + 1] v) := by
  obtain ⟨hrj, hdj⟩ := bfsAncestor_level hr j (by omega)
  have h := (bfsParent_spec hrj (by omega)).1
  simpa only [Function.iterate_succ_apply'] using h

theorem bfsAncestor_injective {V : Type*} {G : SimpleGraph V} {root v : V}
    (hr : G.Reachable root v) {d : ℕ} (hd : d ≤ G.dist root v) :
    Function.Injective (fun i : Fin (d + 1) => (bfsParent G root)^[i.val] v) := by
  intro i j hij
  have hi := (bfsAncestor_level hr i.val (by have := i.isLt; omega)).2
  have hj := (bfsAncestor_level hr j.val (by have := j.isLt; omega)).2
  have hlevel := congrArg (G.dist root) hij
  rw [hi, hj] at hlevel
  apply Fin.ext
  have := i.isLt
  have := j.isLt
  omega

end CycleClique.Construction

end OAI
