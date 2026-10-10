import OAI.Probability.SwitchChain.TripleMatrixEncoding

namespace OAI

noncomputable section
open scoped BigOperators
namespace Problem315.TripleInternalEncoding
attribute [local instance] Classical.propDecidable

variable {W : Type*} [Fintype W]

def adjacencyBit {V : Type*} (G : SimpleGraph V) (u v : V) : ℕ :=
  if G.Adj u v then 1 else 0

def leftDegree (G : SimpleGraph (Fin 3 ⊕ W)) (v : Fin 3) : ℕ :=
  ∑ w, adjacencyBit G (Sum.inl v) w

def crossColumn (G : SimpleGraph (Fin 3 ⊕ W)) (w : W) : ℕ :=
  ∑ v : Fin 3, adjacencyBit G (Sum.inl v) (Sum.inr w)

def internalGraph (G : SimpleGraph (Fin 3 ⊕ W)) : SimpleGraph (Fin 3) :=
  G.comap Sum.inl

def outsideGraph (G : SimpleGraph (Fin 3 ⊕ W)) : SimpleGraph W :=
  G.comap Sum.inr

theorem leftDegree_eq_degree (G : SimpleGraph (Fin 3 ⊕ W)) (v : Fin 3) :
    leftDegree G v = G.degree (Sum.inl v) := by
  simpa only [leftDegree, adjacencyBit, Nat.cast_id] using
    (G.degree_eq_sum_if_adj (R := ℕ) (Sum.inl v)).symm

theorem leftDegree_decompose (G : SimpleGraph (Fin 3 ⊕ W)) (v : Fin 3) :
    leftDegree G v = graphDegree (internalGraph G) v +
      ∑ w, adjacencyBit G (Sum.inl v) (Sum.inr w) := by
  simp only [leftDegree, Fintype.sum_sum_type, graphDegree, Finset.card_eq_sum_ones,
    Finset.sum_filter, internalGraph, SimpleGraph.comap_adj, adjacencyBit]

abbrev GraphTripleCell (O : SimpleGraph W) (e : ℕ) (d : Fin 3 → ℕ) (c : W → ℕ) :=
  {G : SimpleGraph (Fin 3 ⊕ W) // outsideGraph G = O ∧
    internalEdgeCount (internalGraph G) = e ∧
    (∀ v, leftDegree G v = d v) ∧ ∀ w, crossColumn G w = c w}

variable {O : SimpleGraph W} {e : ℕ} {d : Fin 3 → ℕ} {c : W → ℕ}

def graphToCell (G : GraphTripleCell O e d c) : TripleCell W e d c where
  outside v w := adjacencyBit G.val (Sum.inl v) (Sum.inr w)
  inside := internalGraph G.val
  edge_count := G.property.2.1
  binary v w := by unfold adjacencyBit; split <;> omega
  columns w := G.property.2.2.2 w
  rows v := by
    have h := G.property.2.2.1 v
    rw [leftDegree_decompose] at h
    omega

def assembleGraph (O : SimpleGraph W) (A : TripleCell W e d c) :
    SimpleGraph (Fin 3 ⊕ W) where
  Adj x y := match x, y with
    | Sum.inl v, Sum.inl u => A.inside.Adj v u
    | Sum.inl v, Sum.inr w => A.outside v w = 1
    | Sum.inr w, Sum.inl v => A.outside v w = 1
    | Sum.inr w, Sum.inr z => O.Adj w z
  symm := by
    constructor
    intro x y h
    cases x with
    | inl v =>
        cases y with
        | inl u => exact A.inside.symm.symm v u h
        | inr w => exact h
    | inr w =>
        cases y with
        | inl v => exact h
        | inr z => exact O.symm.symm w z h
  loopless := by
    constructor
    intro x h
    cases x with
    | inl v => exact A.inside.loopless.irrefl v h
    | inr w => exact O.loopless.irrefl w h

@[simp] theorem internalGraph_assemble (O : SimpleGraph W) (A : TripleCell W e d c) :
    internalGraph (assembleGraph O A) = A.inside := by
  ext v u
  rfl

@[simp] theorem outsideGraph_assemble (O : SimpleGraph W) (A : TripleCell W e d c) :
    outsideGraph (assembleGraph O A) = O := by
  ext w z
  rfl

@[simp] theorem adjacencyBit_assemble_cross (O : SimpleGraph W)
    (A : TripleCell W e d c) (v : Fin 3) (w : W) :
    adjacencyBit (assembleGraph O A) (Sum.inl v) (Sum.inr w) = A.outside v w := by
  unfold adjacencyBit
  have h := A.binary v w
  split_ifs with hedge
  · exact (show A.outside v w = 1 from hedge).symm
  · have hne : A.outside v w ≠ 1 := hedge
    omega

def cellToGraph (O : SimpleGraph W) (A : TripleCell W e d c) :
    GraphTripleCell O e d c :=
  ⟨assembleGraph O A, outsideGraph_assemble O A, by
    rw [internalGraph_assemble]; exact A.edge_count, by
    intro v
    rw [leftDegree_decompose, internalGraph_assemble]
    simp only [adjacencyBit_assemble_cross]
    have h := A.rows v
    omega, by
    intro w
    simpa only [crossColumn, adjacencyBit_assemble_cross] using A.columns w⟩

@[simp] theorem graphToCell_cellToGraph (O : SimpleGraph W) (A : TripleCell W e d c) :
    graphToCell (cellToGraph O A) = A := by
  apply TripleCell.ext
  · funext v w
    exact adjacencyBit_assemble_cross O A v w
  · exact internalGraph_assemble O A

@[simp] theorem cellToGraph_graphToCell (G : GraphTripleCell O e d c) :
    cellToGraph O (graphToCell G) = G := by
  apply Subtype.ext
  ext x y
  cases x with
  | inl v =>
      cases y with
      | inl u => rfl
      | inr w => simp [cellToGraph, assembleGraph, graphToCell, adjacencyBit]
  | inr w =>
      cases y with
      | inl v =>
          simpa [cellToGraph, assembleGraph, graphToCell, adjacencyBit] using
            G.val.adj_comm (Sum.inl v) (Sum.inr w)
      | inr z =>
          change O.Adj w z ↔ G.val.Adj (Sum.inr w) (Sum.inr z)
          exact Iff.of_eq (congrArg (fun K : SimpleGraph W => K.Adj w z) G.property.1).symm

def graphTripleCellEquiv (O : SimpleGraph W) (e : ℕ) (d : Fin 3 → ℕ) (c : W → ℕ) :
    GraphTripleCell O e d c ≃ TripleCell W e d c where
  toFun := graphToCell
  invFun := cellToGraph O
  left_inv := cellToGraph_graphToCell
  right_inv := graphToCell_cellToGraph O

def graphTripleMatrixEquiv (O : SimpleGraph W) (e : ℕ) (he : e ≤ 3)
    (d : Fin 3 → ℕ) (c : W → ℕ) (hd : ∀ v, rowOffset e ≤ d v) :
    GraphTripleCell O e d c ≃ AugmentedMatrix W e d c :=
  (graphTripleCellEquiv O e d c).trans (tripleMatrixEquiv e he d c hd)

end Problem315.TripleInternalEncoding

end

end OAI
