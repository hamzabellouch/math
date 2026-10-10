import Mathlib

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem315.DisjointBlock

abbrev Vertex (O : Type*) := Fin 2 ⊕ (Fin 2 ⊕ O)

structure Data (O : Type*) where
  outside : SimpleGraph O
  internalA : Bool
  internalB : Bool
  cross : Fin 2 → Fin 2 → Bool
  outsideA : Fin 2 → O → Bool
  outsideB : Fin 2 → O → Bool

variable {O : Type*}

def adjacency (D : Data O) : Vertex O → Vertex O → Prop
  | Sum.inl i, Sum.inl j => i ≠ j ∧ D.internalA = true
  | Sum.inl i, Sum.inr (Sum.inl j) => D.cross i j = true
  | Sum.inl i, Sum.inr (Sum.inr o) => D.outsideA i o = true
  | Sum.inr (Sum.inl i), Sum.inl j => D.cross j i = true
  | Sum.inr (Sum.inl i), Sum.inr (Sum.inl j) => i ≠ j ∧ D.internalB = true
  | Sum.inr (Sum.inl i), Sum.inr (Sum.inr o) => D.outsideB i o = true
  | Sum.inr (Sum.inr o), Sum.inl i => D.outsideA i o = true
  | Sum.inr (Sum.inr o), Sum.inr (Sum.inl i) => D.outsideB i o = true
  | Sum.inr (Sum.inr o), Sum.inr (Sum.inr p) => D.outside.Adj o p

def graph (D : Data O) : SimpleGraph (Vertex O) where
  Adj := adjacency D
  symm := by
    constructor
    intro x y h
    rcases x with i | i | o <;> rcases y with j | j | p
    all_goals dsimp [adjacency] at h ⊢
    all_goals first | exact h | exact ⟨Ne.symm h.1, h.2⟩ | exact D.outside.symm.symm _ _ h
  loopless := by
    constructor
    intro x h
    rcases x with i | i | o
    · exact h.1 rfl
    · exact h.1 rfl
    · exact D.outside.loopless.irrefl o h

def encode (G : SimpleGraph (Vertex O)) : Data O := by
  classical
  exact {
    outside := G.comap (fun o => Sum.inr (Sum.inr o))
    internalA := decide (G.Adj (Sum.inl 0) (Sum.inl 1))
    internalB := decide (G.Adj (Sum.inr (Sum.inl 0)) (Sum.inr (Sum.inl 1)))
    cross := fun i j => decide (G.Adj (Sum.inl i) (Sum.inr (Sum.inl j)))
    outsideA := fun i o => decide (G.Adj (Sum.inl i) (Sum.inr (Sum.inr o)))
    outsideB := fun i o => decide (G.Adj (Sum.inr (Sum.inl i)) (Sum.inr (Sum.inr o))) }

 theorem graph_encode (G : SimpleGraph (Vertex O)) : graph (encode G) = G := by
  classical
  ext x y
  rcases x with i | i | o <;> rcases y with j | j | p
  all_goals simp only [graph, adjacency, encode, decide_eq_true_eq, SimpleGraph.comap_adj]
  · fin_cases i <;> fin_cases j <;> simp [G.adj_comm]
  · exact G.adj_comm _ _
  · fin_cases i <;> fin_cases j <;> simp [G.adj_comm]
  · exact G.adj_comm _ _
  · exact G.adj_comm _ _

 theorem encode_graph (D : Data O) : encode (graph D) = D := by
  classical
  rcases D with ⟨H, a, b, M, U, W⟩
  unfold encode graph
  congr 1 <;> simp [adjacency]
  all_goals
    funext vertex neighbor
    apply Bool.eq_iff_iff.mpr
    exact @decide_eq_true_iff _ (Classical.propDecidable _)

def graphEquiv : SimpleGraph (Vertex O) ≃ Data O where
  toFun := encode
  invFun := graph
  left_inv := graph_encode
  right_inv := encode_graph

def indicator (p : Prop) : ℕ := by
  classical
  exact if p then 1 else 0

def valence {V : Type*} [Fintype V] (G : SimpleGraph V) (v : V) : ℕ :=
  ∑ w, indicator (G.Adj v w)

 theorem valence_eq_degree {V : Type*} [Fintype V] (G : SimpleGraph V) (v : V)
    [Fintype (G.neighborSet v)] : valence G v = G.degree v := by
  classical
  have hset : Finset.univ.filter (G.Adj v) = G.neighborFinset v := by
    ext w
    simp
  rw [← G.card_neighborFinset_eq_degree, ← hset]
  simp only [valence, indicator, Finset.card_eq_sum_ones, Finset.sum_filter]

 theorem internal_indicator_sum (a : Bool) (i : Fin 2) :
    (∑ j : Fin 2, indicator (i ≠ j ∧ a = true)) = a.toNat := by
  fin_cases i <;> cases a <;> norm_num [indicator, Fin.sum_univ_two]

 theorem bool_indicator (b : Bool) : indicator (b = true) = b.toNat := by
  cases b <;> simp [indicator]

theorem valence_graph_A [Fintype O] (D : Data O) (i : Fin 2) :
    valence (graph D) (Sum.inl i) = D.internalA.toNat +
      (∑ j, (D.cross i j).toNat) + ∑ o, (D.outsideA i o).toNat := by
  simp only [valence, Fintype.sum_sum_type, graph, adjacency,
    internal_indicator_sum, bool_indicator]
  omega

theorem valence_graph_B [Fintype O] (D : Data O) (j : Fin 2) :
    valence (graph D) (Sum.inr (Sum.inl j)) = D.internalB.toNat +
      (∑ i, (D.cross i j).toNat) + ∑ o, (D.outsideB j o).toNat := by
  simp only [valence, Fintype.sum_sum_type, graph, adjacency,
    internal_indicator_sum, bool_indicator]
  omega

theorem valence_graph_outside [Fintype O] (D : Data O) (o : O) :
    valence (graph D) (Sum.inr (Sum.inr o)) = valence D.outside o +
      (∑ i, (D.outsideA i o).toNat) + ∑ j, (D.outsideB j o).toNat := by
  simp only [valence, Fintype.sum_sum_type, graph, adjacency, bool_indicator]
  omega

end Problem315.DisjointBlock

end

end OAI
