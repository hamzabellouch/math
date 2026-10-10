import OAI.Combinatorics.Crossing.TwoTriangleBasis
import Mathlib.Data.Finset.Sort

namespace OAI

noncomputable section
namespace Zarankiewicz
open scoped BigOperators

abbrev OrderedNode (s : ℕ) := ↥(Finset.Icc 1 (2*s+1))

@[simp] theorem card_orderedNode (s : ℕ) : Fintype.card (OrderedNode s) = 2*s+1 := by
  simp [OrderedNode, Nat.card_Icc]

def extendOrderedNode (s : ℕ) (node : OrderedNode s → ℝ) (i : ℕ) : ℝ :=
  if hi : i ∈ Finset.Icc 1 (2*s+1) then node ⟨i,hi⟩ else 0

@[simp] theorem extendOrderedNode_apply (s : ℕ) (node : OrderedNode s → ℝ) (i : OrderedNode s) :
    extendOrderedNode s node i.val = node i := by
  simp [extendOrderedNode, i.property]

theorem extendOrderedNode_injOn (s : ℕ) (node : OrderedNode s → ℝ)
    (hn : Function.Injective node) : Set.InjOn (extendOrderedNode s node) (Set.Icc 1 (2*s+1)) := by
  intro p hp q hq he
  have hp' : p ∈ Finset.Icc 1 (2*s+1) := Finset.mem_Icc.mpr hp
  have hq' : q ∈ Finset.Icc 1 (2*s+1) := Finset.mem_Icc.mpr hq
  simp only [extendOrderedNode, dite_eq_left hp', dite_eq_left hq'] at he
  exact congrArg Subtype.val (hn he)

theorem triangle_nodes_mem {s p q : ℕ} (h : (p,q) ∈ twoTriangle s) :
    p ∈ Finset.Icc 1 (2*s+1) ∧ q ∈ Finset.Icc 1 (2*s+1) := by
  rw [mem_twoTriangle] at h
  simp only [Finset.mem_Icc]
  omega

def triangleNodePair (s : ℕ) (pq : TriangleIndex s) : OrderedNode s × OrderedNode s :=
  (⟨pq.val.1, (triangle_nodes_mem pq.property).1⟩,
    ⟨pq.val.2, (triangle_nodes_mem pq.property).2⟩)

theorem triangleNodePair_injective (s : ℕ) : Function.Injective (triangleNodePair s) := by
  intro p q he
  apply Subtype.ext
  exact congrArg (fun pq : OrderedNode s × OrderedNode s => (pq.1.val,pq.2.val)) he

def orderedTriangle (s : ℕ) : Finset (OrderedNode s × OrderedNode s) :=
  Finset.univ.filter (fun pq => (pq.1.val,pq.2.val) ∈ twoTriangle s)

def triangleNodeEquiv (s : ℕ) : TriangleIndex s ≃ ↥(orderedTriangle s) where
  toFun pq := ⟨triangleNodePair s pq, by simp [orderedTriangle, triangleNodePair, pq.property]⟩
  invFun pq := ⟨(pq.val.1.val,pq.val.2.val), by simpa [orderedTriangle] using pq.property⟩
  left_inv pq := rfl
  right_inv pq := rfl

theorem triangleMatrix_ordered_entry (s : ℕ) (node : OrderedNode s → ℝ)
    (ab j : BiExponent s) :
    triangleMatrix s (extendOrderedNode s node) ab j =
      node (triangleNodePair s (triangleCoordEquiv s j)).1 ^ ab.1.val *
      node (triangleNodePair s (triangleCoordEquiv s j)).2 ^ ab.2.val := by
  unfold triangleMatrix monomialVector
  change extendOrderedNode s node (triangleNodePair s (triangleCoordEquiv s j)).1.val ^ ab.1.val *
    extendOrderedNode s node (triangleNodePair s (triangleCoordEquiv s j)).2.val ^ ab.2.val = _
  rw [extendOrderedNode_apply, extendOrderedNode_apply]

end Zarankiewicz

end

end OAI
