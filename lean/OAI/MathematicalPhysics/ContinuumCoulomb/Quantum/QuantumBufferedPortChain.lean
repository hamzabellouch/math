import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumPortRouteData
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumBufferedNodes
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumBufferedSharedEdge
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumRoutedSubdivision

namespace OAI

/-! The actual bounded spatial routes give distinct physical spin locations at every
cell port, including cells at which two coarse routes cross. -/

noncomputable section
namespace ContinuumCoulomb
open scoped Classical
namespace QMASpatialExchangeModel
variable {A B : ℕ} (M : QMASpatialExchangeModel A B)

abbrev exchangeGraph : QMARationalExchangeGraph where
  n := M.n
  Edge := M.Term
  left := M.left
  right := M.right
  distinct := M.distinct
  weight := M.weight
  constant := M.constant

@[simp] theorem exchangeGraph_energy : M.exchangeGraph.energy = M.energy := rfl

def coarseRoute (hd : ∀ v, qmaGraphDegree M.left M.right v ≤ 3) (e : M.Term) (i : ℕ) : ℕ × ℕ :=
  (M.bufferedPath hd e).val.getVert i

def coarseLength (hd : ∀ v, qmaGraphDegree M.left M.right v ≤ 3) (e : M.Term) : ℕ :=
  (M.bufferedPath hd e).val.length

theorem coarseLength_pos (hd : ∀ v, qmaGraphDegree M.left M.right v ≤ 3) (e : M.Term) :
    0 < M.coarseLength hd e := by
  by_contra h
  have hz : (M.bufferedPath hd e).val.length = 0 := by exact Nat.eq_zero_of_not_pos h
  have he := (M.bufferedPath hd e).val.getVert_length
  rw [hz,SimpleGraph.Walk.getVert_zero] at he
  exact M.distinct e (M.placedVertex_injective he)

@[simp] theorem coarseRoute_zero (hd : ∀ v, qmaGraphDegree M.left M.right v ≤ 3) (e : M.Term) :
    M.coarseRoute hd e 0 = M.placedVertex (M.left e) := SimpleGraph.Walk.getVert_zero _

@[simp] theorem coarseRoute_last (hd : ∀ v, qmaGraphDegree M.left M.right v ≤ 3) (e : M.Term) :
    M.coarseRoute hd e (M.coarseLength hd e) = M.placedVertex (M.right e) :=
  SimpleGraph.Walk.getVert_length _

theorem coarseRoute_step (hd : ∀ v, qmaGraphDegree M.left M.right v ≤ 3) (e : M.Term)
    (i : ℕ) (hi : i < M.coarseLength hd e) :
    qmaSquareGrid.Adj (M.coarseRoute hd e i) (M.coarseRoute hd e (i+1)) :=
  qmaGridPath_getVert_step (M.bufferedPath hd e) ⟨i,hi⟩

theorem coarseRoute_positive (hd : ∀ v, qmaGraphDegree M.left M.right v ≤ 3)
    (e : M.Term) (i : ℕ) : 0 < (M.coarseRoute hd e i).1 ∧ 0 < (M.coarseRoute hd e i).2 :=
  M.bufferedPath_positive hd e ((M.bufferedPath hd e).val.getVert_mem_support i)

theorem coarseRoute_simple (hd : ∀ v, qmaGraphDegree M.left M.right v ≤ 3)
    (e : M.Term) (i j : ℕ) (hi : i ≤ M.coarseLength hd e) (hj : j ≤ M.coarseLength hd e)
    (he : M.coarseRoute hd e i = M.coarseRoute hd e j) : i = j :=
  (M.bufferedPath hd e).property.getVert_injOn hi hj he

theorem coarseRoute_edges_disjoint (hA : 0 < A)
    (hd : ∀ v, qmaGraphDegree M.left M.right v ≤ 3) {e f : M.Term} (hef : e ≠ f)
    (i j : ℕ) (hi : i < M.coarseLength hd e) (hj : j < M.coarseLength hd f) :
    ¬(M.coarseRoute hd e i = M.coarseRoute hd f j ∧
        M.coarseRoute hd e (i+1) = M.coarseRoute hd f (j+1)) ∧
      ¬(M.coarseRoute hd e i = M.coarseRoute hd f (j+1) ∧
        M.coarseRoute hd e (i+1) = M.coarseRoute hd f j) := by
  have he : s(M.coarseRoute hd e i,M.coarseRoute hd e (i+1)) ∈ (M.bufferedPath hd e).val.edges :=
    ((M.bufferedPath hd e).val.mk_mem_edges_iff_exists).mpr ⟨i,hi,rfl⟩
  have hf : s(M.coarseRoute hd f j,M.coarseRoute hd f (j+1)) ∈ (M.bufferedPath hd f).val.edges :=
    ((M.bufferedPath hd f).val.mk_mem_edges_iff_exists).mpr ⟨j,hj,rfl⟩
  constructor
  · rintro ⟨h1,h2⟩
    rw [h1,h2] at he
    exact M.bufferedPath_no_shared_edge hA hd hef he hf
  · rintro ⟨h1,h2⟩
    rw [h1,h2,Sym2.eq_swap] at he
    exact M.bufferedPath_no_shared_edge hA hd hef he hf

abbrev portSchedule (hd : ∀ v, qmaGraphDegree M.left M.right v ≤ 3) : QMAPathSchedule where
  graph := M.exchangeGraph
  work := M.coarseLength hd

def portGraph (hd : ∀ v, qmaGraphDegree M.left M.right v ≤ 3) : SimpleGraph (ℕ × ℕ) :=
  SimpleGraph.fromRel (fun x y => ∃ (e : M.Term) (k : ℕ), k < 2*M.coarseLength hd e+1 ∧
    qmaPortChain (M.coarseRoute hd e) (M.coarseLength hd e) k = x ∧
    qmaPortChain (M.coarseRoute hd e) (M.coarseLength hd e) (k+1) = y)

theorem portChain_first (hd : ∀ v, qmaGraphDegree M.left M.right v ≤ 3) (e : M.Term) :
    qmaPortChain (M.coarseRoute hd e) (M.coarseLength hd e) 0 =
      qmaExpandedPoint (M.placedVertex (M.left e)) := by
  rw [qmaPortChain_zero]
  exact congrArg qmaExpandedPoint (M.coarseRoute_zero hd e)

theorem portChain_last (hd : ∀ v, qmaGraphDegree M.left M.right v ≤ 3) (e : M.Term) :
    qmaPortChain (M.coarseRoute hd e) (M.coarseLength hd e) (2*M.coarseLength hd e+1) =
      qmaExpandedPoint (M.placedVertex (M.right e)) := by
  rw [qmaPortChain_last]
  exact congrArg qmaExpandedPoint (M.coarseRoute_last hd e)

theorem portChain_simple (hd : ∀ v, qmaGraphDegree M.left M.right v ≤ 3)
    (e : M.Term) (i j : ℕ) (hi : i ≤ 2*M.coarseLength hd e+1) (hj : j ≤ 2*M.coarseLength hd e+1)
    (h : qmaPortChain (M.coarseRoute hd e) (M.coarseLength hd e) i =
      qmaPortChain (M.coarseRoute hd e) (M.coarseLength hd e) j) : i = j :=
  qmaPortChain_injective _ (M.coarseLength_pos hd e)
    (M.coarseRoute_step hd e) (fun k _ => M.coarseRoute_positive hd e k)
    (M.coarseRoute_simple hd e) hi hj h

theorem portChain_step (hd : ∀ v, qmaGraphDegree M.left M.right v ≤ 3)
    (e : M.Term) (i : ℕ) (hi : i < 2*M.coarseLength hd e+1) :
    (M.portGraph hd).Adj
      (qmaPortChain (M.coarseRoute hd e) (M.coarseLength hd e) i)
      (qmaPortChain (M.coarseRoute hd e) (M.coarseLength hd e) (i+1)) := by
  apply (SimpleGraph.fromRel_adj _ _ _).mpr
  refine ⟨?_,Or.inl ⟨e,i,hi,rfl,rfl⟩⟩
  intro h
  have he := M.portChain_simple hd e i (i+1) (Nat.le_of_lt hi) (by omega) h
  omega

theorem portChain_disjoint (hA : 0 < A) (hd : ∀ v, qmaGraphDegree M.left M.right v ≤ 3)
    (e f : M.Term) (i j : ℕ) (hef : e ≠ f) (hi0 : 0 < i)
    (hi : i < 2*M.coarseLength hd e+1) (hj : j ≤ 2*M.coarseLength hd f+1) :
    qmaPortChain (M.coarseRoute hd e) (M.coarseLength hd e) i ≠
      qmaPortChain (M.coarseRoute hd f) (M.coarseLength hd f) j :=
  qmaPortChain_interiors_disjoint _ _ (M.coarseRoute_step hd e) (M.coarseRoute_step hd f)
    (fun k _ => M.coarseRoute_positive hd e k) (fun k _ => M.coarseRoute_positive hd f k)
    (M.coarseRoute_edges_disjoint hA hd hef) hi0 hi hj

def portRouteData (hA : 0 < A) (hd : ∀ v, qmaGraphDegree M.left M.right v ≤ 3) :
    QMAPortRouteData M.exchangeGraph where
  length := M.coarseLength hd
  length_pos := M.coarseLength_pos hd
  position := M.placedVertex
  position_injective := M.placedVertex_injective
  point := M.coarseRoute hd
  first := M.coarseRoute_zero hd
  last := M.coarseRoute_last hd
  simple := M.coarseRoute_simple hd
  step := M.coarseRoute_step hd
  positive := fun e i _ => M.coarseRoute_positive hd e i
  edges_disjoint := fun _e _f hef => M.coarseRoute_edges_disjoint hA hd hef

theorem portRouteData_graph (hA : 0 < A) (hd : ∀ v, qmaGraphDegree M.left M.right v ≤ 3) :
    (M.portRouteData hA hd).graph = M.portGraph hd := rfl

def portEmbedding (hA : 0 < A) (hd : ∀ v, qmaGraphDegree M.left M.right v ≤ 3) :=
  (M.portRouteData hA hd).toEmbedding

end QMASpatialExchangeModel
end ContinuumCoulomb

end

end OAI
