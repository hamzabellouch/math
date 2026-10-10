import OAI.Combinatorics.PortMatching.Basic

namespace OAI

/-! Perfect-matching-preserving port-path degree reduction for finite simple graphs. -/

noncomputable section
namespace Matching205.Forward
universe u

def Pair (c i j : ℕ) : Prop :=
  (i < c ∧ i % 2 = 0 ∧ j = i + 1) ∨
  (j < c ∧ j % 2 = 0 ∧ i = j + 1) ∨
  (c < i ∧ i % 2 = 1 ∧ j = i + 1) ∨
  (c < j ∧ j % 2 = 1 ∧ i = j + 1)

lemma pair_symm {c i j : ℕ} (h : Pair c i j) : Pair c j i := by
  rcases h with h | h | h | h
  · exact Or.inr (Or.inl h)
  · exact Or.inl h
  · exact Or.inr (Or.inr (Or.inr h))
  · exact Or.inr (Or.inr (Or.inl h))

lemma pair_consecutive {c i j : ℕ} (h : Pair c i j) :
    i + 1 = j ∨ j + 1 = i := by
  dsimp [Pair] at h
  omega

lemma pair_not_center {k i j : ℕ} (h : Pair (2 * k) i j) : i ≠ 2 * k := by
  dsimp [Pair] at h
  omega

lemma pair_completion (r k : ℕ) (hk : k < r)
    (i : Fin (2 * r - 1)) (hi : i.val ≠ 2 * k) :
    ∃! j : Fin (2 * r - 1), Pair (2 * k) i.val j.val := by
  have hib := i.isLt
  by_cases hl : i.val < 2 * k
  · by_cases hp : i.val % 2 = 0
    · refine ⟨⟨i.val + 1, by omega⟩, ?_, ?_⟩
      · dsimp [Pair]; omega
      · intro j hj; apply Fin.ext; dsimp [Pair] at hj; dsimp; omega
    · refine ⟨⟨i.val - 1, by omega⟩, ?_, ?_⟩
      · dsimp [Pair]; omega
      · intro j hj; apply Fin.ext; dsimp [Pair] at hj; dsimp; omega
  · by_cases hp : i.val % 2 = 0
    · refine ⟨⟨i.val - 1, by omega⟩, ?_, ?_⟩
      · dsimp [Pair]; omega
      · intro j hj; apply Fin.ext; dsimp [Pair] at hj; dsimp; omega
    · refine ⟨⟨i.val + 1, by omega⟩, ?_, ?_⟩
      · dsimp [Pair]; omega
      · intro j hj; apply Fin.ext; dsimp [Pair] at hj; dsimp; omega

variable {V : Type u} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
variable (M : G.Subgraph) (hM : M.IsPerfectMatching)

omit [Fintype V] [DecidableRel G.Adj] in
include hM in
private lemma unique_neighbor (v : V) : ∃! w, M.Adj v w :=
  SimpleGraph.Subgraph.isPerfectMatching_iff.mp hM v

def neighbor (v : V) : G.neighborSet v :=
  ⟨(unique_neighbor G M hM v).choose,
    M.adj_sub (unique_neighbor G M hM v).choose_spec.1⟩

omit [Fintype V] [DecidableRel G.Adj] in
lemma neighbor_adj (v : V) : M.Adj v (neighbor G M hM v).val :=
  (unique_neighbor G M hM v).choose_spec.1

def center (v : V) : ℕ :=
  2 * ((Fintype.equivFin (G.neighborSet v)) (neighbor G M hM v)).val

def selected (v : V) : Vertex G := port G v (neighbor G M hM v)

lemma port_eq_selected {v w : V} (h : M.Adj v w) :
    port G v ⟨w, M.adj_sub h⟩ = selected G M hM v := by
  have hw : w = (neighbor G M hM v).val :=
    (unique_neighbor G M hM v).choose_spec.2 w h
  have hn : (⟨w, M.adj_sub h⟩ : G.neighborSet v) = neighbor G M hM v :=
    Subtype.ext hw
  exact congrArg (port G v) hn

def Local (x y : Vertex G) : Prop :=
  x.1 = y.1 ∧ Pair (center G M hM x.1) x.2.val y.2.val

def Across (x y : Vertex G) : Prop :=
  External G x y ∧ M.Adj x.1 y.1

lemma local_symm {x y : Vertex G} (h : Local G M hM x y) : Local G M hM y x := by
  refine ⟨h.1.symm, ?_⟩
  have hc : center G M hM x.1 = center G M hM y.1 :=
    congrArg (center G M hM) h.1
  have hp : Pair (center G M hM x.1) y.2.val x.2.val =
      Pair (center G M hM y.1) y.2.val x.2.val :=
    congrArg (fun c : ℕ => Pair c y.2.val x.2.val) hc
  exact hp.mp (pair_symm h.2)

lemma across_symm {x y : Vertex G} (h : Across G M x y) : Across G M y x :=
  ⟨external_symm G h.1, h.2.symm⟩

lemma across_selected {x y : Vertex G} (h : Across G M x y) :
    x = selected G M hM x.1 := by
  obtain ⟨hg, hx, _⟩ := h.1
  exact hx.trans (port_eq_selected G M hM h.2)

include hM in
lemma across_unique {x y z : Vertex G}
    (hy : Across G M x y) (hz : Across G M x z) : y = z := by
  have hv : y.1 = z.1 := hM.1.eq_of_adj_left hy.2 hz.2
  calc
    y = selected G M hM y.1 := across_selected G M hM (across_symm G M hy)
    _ = selected G M hM z.1 := congrArg (selected G M hM) hv
    _ = z := (across_selected G M hM (across_symm G M hz)).symm

lemma selected_across (v : V) : ∃ y, Across G M (selected G M hM v) y := by
  let w := neighbor G M hM v
  let h : G.Adj v w.val := w.property
  refine ⟨port G w.val ⟨v, h.symm⟩, ?_⟩
  exact ⟨⟨h, rfl, rfl⟩, neighbor_adj G M hM v⟩

lemma local_not_selected {x y : Vertex G} (h : Local G M hM x y) :
    x ≠ selected G M hM x.1 := by
  intro hx
  have hp := pair_not_center h.2
  apply hp
  have hv := congrArg (fun z : Vertex G => z.2.val) hx
  exact hv

lemma local_completion (x : Vertex G) (hx : x ≠ selected G M hM x.1) :
    ∃! y, Local G M hM x y := by
  rcases x with ⟨v, i⟩
  let k := (Fintype.equivFin (G.neighborSet v)) (neighbor G M hM v)
  have hi : i.val ≠ 2 * k.val := by
    intro hi
    apply hx
    have hfin : i = (selected G M hM v).2 := Fin.ext hi
    cases hfin
    rfl
  obtain ⟨j, hj, hu⟩ := pair_completion (arity G v) k.val k.isLt i hi
  refine ⟨⟨v, j⟩, ⟨rfl, hj⟩, ?_⟩
  rintro ⟨w, l⟩ ⟨hw, hl⟩
  dsimp at hw
  subst w
  have hlj : l = j := hu l hl
  cases hlj
  rfl

def extend : (graph G).Subgraph where
  verts := Set.univ
  Adj x y := Local G M hM x y ∨ Across G M x y
  adj_sub := by
    intro x y h
    rcases h with h | h
    · exact Or.inl ⟨h.1, pair_consecutive h.2⟩
    · exact Or.inr h.1
  edge_vert := fun _ => Set.mem_univ _
  symm := ⟨by
    intro x y h
    exact h.elim (fun h => Or.inl (local_symm G M hM h))
      (fun h => Or.inr (across_symm G M h))⟩

theorem extend_perfect : (extend G M hM).IsPerfectMatching := by
  classical
  apply SimpleGraph.Subgraph.isPerfectMatching_iff.mpr
  intro x
  by_cases hx : x = selected G M hM x.1
  · obtain ⟨y, hy⟩ := selected_across G M hM x.1
    have hy' : Across G M x y := hx.symm ▸ hy
    refine ⟨y, Or.inr hy', ?_⟩
    intro z hz
    rcases hz with hz | hz
    · exact False.elim (local_not_selected G M hM hz hx)
    · exact across_unique G M hM hz hy'
  · obtain ⟨y, hy, hu⟩ := local_completion G M hM x hx
    refine ⟨y, Or.inl hy, ?_⟩
    intro z hz
    rcases hz with hz | hz
    · exact hu z hz
    · exact False.elim (hx (across_selected G M hM hz))

theorem decode_extend_adj (v w : V) :
    (decode G (extend G M hM)).Adj v w ↔ M.Adj v w := by
  constructor
  · rintro ⟨h, hm⟩
    rcases hm with hi | he
    · have hvw : v = w := hi.1
      subst w
      exact False.elim (G.irrefl h)
    · exact he.2
  · intro h
    exact ⟨M.adj_sub h, Or.inr ⟨⟨M.adj_sub h, rfl, rfl⟩, h⟩⟩

end Matching205.Forward

end

end OAI
