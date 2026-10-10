import Mathlib
import OAI.Combinatorics.KMedian.Amplification.Amplifier
import OAI.Combinatorics.KMedian.Machines.CardBounds

namespace OAI

section Inline_PCPAmplifierSize

namespace MetricKMedian.PCP
open Finset
open scoped BigOperators Classical

namespace Amplifier
abbrev WalkData := (Fin radius → Fin (steps+1)) × (Fin radius → Degree)
@[irreducible] noncomputable def walkCoeff : ℕ := Nat.card WalkData
@[irreducible] noncomputable def nodeCoeff : ℕ := 2*ExpanderFamily.growth^2
scoped notation "edgeCoefficient" => (walkCoeff*nodeCoeff*(4*Nat.card (AlphabetReduction.EdgeSample Bits)))
scoped notation "sizeCoefficient" => (nodeCoeff*Nat.card (BitVector Bits)+
  walkCoeff*nodeCoeff*(AlphabetReduction.interiorBound Bits+Nat.card (AlphabetReduction.EdgeSample Bits))+edgeCoefficient)

variable {V E : Type} [Fintype V] [Fintype E] [Nonempty E]
variable (C : BinaryCSP V E Label)
omit [Fintype V] in
lemma powered_edge_card : Nat.card (Edge C)=walkCoeff*Nat.card (Node C) := by
  let e : Edge C ≃ Node C × WalkData :=
    ((Equiv.prodCongr (Equiv.refl _) PortGraph.Walk.wordEquiv).trans
      (Equiv.prodAssoc _ _ _).symm).trans
      ((Equiv.prodCongr (Equiv.prodComm _ _) (Equiv.refl _)).trans (Equiv.prodAssoc _ _ _))
  calc
    _ = Nat.card (Node C × WalkData) := Nat.card_congr e
    _ = Nat.card (Node C)*Nat.card WalkData := Nat.card_prod _ _
    _ = _ := by unfold walkCoeff; exact Nat.mul_comm _ _
omit [Fintype V] in
lemma node_card_bound : Nat.card (Node C) ≤ nodeCoeff*Nat.card E :=
  by simpa only [← Nat.card_eq_fintype_card, nodeCoeff, Node] using GlobalRegularization.node_upper C
omit [Fintype V] in
lemma edge_card_formula : Nat.card (NewEdge C)=Nat.card (Edge C)*(4*Nat.card (AlphabetReduction.EdgeSample Bits)) := by
  change Nat.card ((Edge C × AlphabetReduction.EdgeSample Bits) × Fin 4)=_
  rw [Nat.card_prod,Nat.card_prod,Nat.card_fin]
  rw [Nat.mul_assoc, Nat.mul_comm (Nat.card (AlphabetReduction.EdgeSample Bits)) 4]
private lemma arith_edge_bound (v e w n z : ℕ) (h : v≤n*e) : (w*v)*z≤(w*n*z)*e := by
  calc
    _ ≤ (w*(n*e))*z := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ h)
    _ = _ := by ring
private lemma arith_edge_chain (a b v e w n z : ℕ)
    (h1 : a=b*z) (h2 : b=w*v) (h3 : v≤n*e) : a≤w*n*z*e := by
  rw [h1,h2]
  exact arith_edge_bound v e w n z h3
omit [Fintype V] in
lemma edge_card_bound : Nat.card (NewEdge C) ≤
    (walkCoeff*nodeCoeff*(4*Nat.card (AlphabetReduction.EdgeSample Bits)))*Nat.card E :=
  arith_edge_chain (Nat.card (NewEdge C)) (Nat.card (Edge C)) (Nat.card (Node C))
    (Nat.card E) walkCoeff nodeCoeff (4*Nat.card (AlphabetReduction.EdgeSample Bits))
    (edge_card_formula C) (powered_edge_card C) (node_card_bound C)
omit [Fintype V] in
lemma node_size_card : Nat.card (NewNode C) ≤ Nat.card (Node C)*Nat.card (BitVector Bits)+
    Nat.card (Edge C)*(AlphabetReduction.interiorBound Bits+Nat.card (AlphabetReduction.EdgeSample Bits)) :=
  (AlphabetReduction.binary_card_bounds_nat (bits C)).1
private lemma arith_size_chain2 (a b v e t w n q z r : ℕ)
    (ha : a ≤ v*q+t*z) (ht : t=w*v) (hv : v ≤ n*e) (hb : b ≤ (w*n*r)*e) :
    a+b ≤ (n*q+w*n*z+w*n*r)*e := by
  subst t
  calc
    _ ≤ (n*e)*q+(w*(n*e))*z+(w*n*r)*e := by
      apply Nat.add_le_add (ha.trans ?_) hb
      exact Nat.add_le_add (Nat.mul_le_mul_right _ hv)
        (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hv))
    _ = _ := by ring
omit [Fintype V] in
lemma size_bound : Nat.card (NewNode C)+Nat.card (NewEdge C) ≤
    (nodeCoeff*Nat.card (BitVector Bits)+walkCoeff*nodeCoeff*(AlphabetReduction.interiorBound Bits+
      Nat.card (AlphabetReduction.EdgeSample Bits))+walkCoeff*nodeCoeff*(4*Nat.card (AlphabetReduction.EdgeSample Bits)))*Nat.card E :=
  arith_size_chain2 (Nat.card (NewNode C)) (Nat.card (NewEdge C)) (Nat.card (Node C))
    (Nat.card E) (Nat.card (Edge C)) walkCoeff nodeCoeff (Nat.card (BitVector Bits))
    (AlphabetReduction.interiorBound Bits+Nat.card (AlphabetReduction.EdgeSample Bits))
    (4*Nat.card (AlphabetReduction.EdgeSample Bits))
    (node_size_card C) (powered_edge_card C) (node_card_bound C) (edge_card_bound C)
noncomputable instance newEdgeNonempty : Nonempty (NewEdge C) := by
  change Nonempty ((Edge C × AlphabetReduction.EdgeSample Bits) × Fin 4)
  let : Nonempty (Edge C) := ⟨(fun _ => 0, PortGraph.Walk.ofWord
    (Classical.arbitrary (Node C)) (fun _ => Classical.arbitrary Degree))⟩
  infer_instance
end Amplifier
end MetricKMedian.PCP

end Inline_PCPAmplifierSize

end OAI
