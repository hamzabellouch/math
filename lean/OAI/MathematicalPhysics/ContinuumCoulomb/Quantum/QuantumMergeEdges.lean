import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumRationalPathStep

namespace OAI

/-! Parallel interactions are combined at one canonically ordered physical edge.
This is an exact matrix operation, with no perturbative error. -/

noncomputable section
namespace ContinuumCoulomb
open scoped BigOperators Classical
namespace QMARationalExchangeGraph

def orderedPair (G : QMARationalExchangeGraph) (e : G.Edge) : Fin G.n × Fin G.n :=
  (min (G.left e) (G.right e),max (G.left e) (G.right e))

def edgePairs (G : QMARationalExchangeGraph) : Finset (Fin G.n × Fin G.n) :=
  Finset.univ.image G.orderedPair

abbrev MergedEdge (G : QMARationalExchangeGraph) := {p // p ∈ G.edgePairs}

def edgeClass (G : QMARationalExchangeGraph) (e : G.Edge) : G.MergedEdge :=
  ⟨G.orderedPair e,Finset.mem_image.mpr ⟨e,Finset.mem_univ _,rfl⟩⟩

theorem orderedPair_lt (G : QMARationalExchangeGraph) (e : G.Edge) :
    (G.orderedPair e).1 < (G.orderedPair e).2 := by
  rcases lt_or_gt_of_ne (G.distinct e) with h | h
  · simpa only [orderedPair,min_eq_left h.le,max_eq_right h.le] using h
  · simpa only [orderedPair,min_eq_right h.le,max_eq_left h.le] using h

theorem mergedEdge_lt (G : QMARationalExchangeGraph) (p : G.MergedEdge) : p.val.1 < p.val.2 := by
  obtain ⟨e,_,he⟩ := Finset.mem_image.mp p.property
  rw [← he]
  exact G.orderedPair_lt e

theorem orderedPair_matrix (G : QMARationalExchangeGraph) (e : G.Edge) :
    sourceHeisenbergMatrix G.n (G.orderedPair e).1 (G.orderedPair e).2 =
      sourceHeisenbergMatrix G.n (G.left e) (G.right e) := by
  rcases le_total (G.left e) (G.right e) with h | h
  · simp only [orderedPair,min_eq_left h,max_eq_right h]
  · simpa only [orderedPair,min_eq_right h,max_eq_left h] using
      qmaHeisenberg_symm G.n (G.right e) (G.left e)

def merge (G : QMARationalExchangeGraph) : QMARationalExchangeGraph where
  n := G.n
  Edge := G.MergedEdge
  left := fun p => p.val.1
  right := fun p => p.val.2
  distinct := fun p => (G.mergedEdge_lt p).ne
  weight := fun p => ∑ e, if G.edgeClass e = p then G.weight e else 0
  constant := G.constant

theorem merge_matrix (G : QMARationalExchangeGraph) :
    qmaExchangeMatrix G.merge.left G.merge.right (fun e => (G.merge.weight e:ℝ)) G.merge.constant =
      qmaExchangeMatrix G.left G.right (fun e => (G.weight e:ℝ)) G.constant := by
  unfold qmaExchangeMatrix
  congr 1
  change (∑ p : G.MergedEdge,
    (((∑ e, if G.edgeClass e = p then G.weight e else 0):ℚ):ℂ) •
      sourceHeisenbergMatrix G.n p.val.1 p.val.2) = _
  push_cast
  simp only [Finset.sum_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e _
  have hcast (p : G.MergedEdge) : (((if G.edgeClass e = p then G.weight e else 0):ℚ):ℂ) =
      (if G.edgeClass e = p then (G.weight e:ℂ) else 0) := by split_ifs <;> simp
  simp_rw [hcast,ite_smul,zero_smul]
  rw [Finset.sum_ite_eq]
  simp only [Finset.mem_univ,ite_true]
  rw [show (G.edgeClass e).val = G.orderedPair e from rfl,G.orderedPair_matrix]

theorem merge_energy (G : QMARationalExchangeGraph) : G.merge.energy = G.energy := by
  unfold energy
  rw [G.merge_matrix]
  rfl

theorem merge_pair_injective (G : QMARationalExchangeGraph) :
    Function.Injective (fun e : G.merge.Edge => (G.merge.left e,G.merge.right e)) := by
  intro e f h
  exact Subtype.ext h

theorem merge_edge_count (G : QMARationalExchangeGraph) : Fintype.card G.merge.Edge ≤ Fintype.card G.Edge := by
  change Fintype.card G.MergedEdge ≤ _
  rw [Fintype.card_coe]
  exact (Finset.card_image_le).trans_eq (Finset.card_univ)

theorem merge_edge_source (G : QMARationalExchangeGraph) (p : G.merge.Edge) :
    ∃ e : G.Edge, (G.merge.left p = G.left e ∧ G.merge.right p = G.right e) ∨
      (G.merge.left p = G.right e ∧ G.merge.right p = G.left e) := by
  obtain ⟨e,_,he⟩ := Finset.mem_image.mp p.property
  refine ⟨e,?_⟩
  change (p.val.1 = G.left e ∧ p.val.2 = G.right e) ∨
    (p.val.1 = G.right e ∧ p.val.2 = G.left e)
  rw [← he]
  rcases le_total (G.left e) (G.right e) with h | h
  · exact Or.inl ⟨min_eq_left h,max_eq_right h⟩
  · exact Or.inr ⟨min_eq_right h,max_eq_left h⟩

end QMARationalExchangeGraph
end ContinuumCoulomb

end

end OAI
