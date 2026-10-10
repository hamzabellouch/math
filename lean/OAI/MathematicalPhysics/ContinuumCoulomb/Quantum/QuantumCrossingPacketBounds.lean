import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumComputedCrossingBounds

namespace OAI

/-! Coefficient bounds for the actual serialized crossing packet.  The
transfer uses the literal nine-bond blocks, including the scalar offset. -/

noncomputable section
namespace ContinuumCoulomb.QuantumCrossingListLayer
open MediatorListProgram QuantumCrossingListBlock
open scoped Classical

variable {r m : ℕ} (C : QMARationalCrossingLayer r) (N : ℚ)
    (labels : C.base.Edge ≃ Fin m)

theorem actual_bonds_coefficientBound {L : ℝ}
    (hc : (C.output N).CoefficientBound L) :
    ∀ b ∈ bonds (actualInput C N labels), |(b.2.2 : ℝ)| ≤ L := by
  intro b hb
  rcases List.mem_append.mp hb with hb | hb
  · obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hb
    exact hc.2 (.inl (.inl (labels.symm i)))
  · have hf : familyInput (actualInput C N labels) =
        ((C.base.n,C.scale N),List.ofFn (actualCrossing C)) := by
      unfold familyInput
      rw [parameters_actual]
      rfl
    rw [hf,family_ofFn] at hb
    obtain ⟨bs,hbs,hb⟩ := List.mem_flatten.mp hb
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hbs
    obtain ⟨k,rfl⟩ := List.mem_ofFn.mp hb
    rw [bond_actual]
    exact hc.2 (edgeTag C N i k)

theorem actualGraph_coefficientBound {L : ℝ}
    (hc : (C.output N).CoefficientBound L) :
    (actualGraph C N labels).CoefficientBound L := by
  constructor
  · change |(constant (actualInput C N labels) : ℝ)| ≤ L
    rw [constant_actual]
    exact hc.1
  · intro e
    exact actual_bonds_coefficientBound C N labels hc _
      (List.get_mem (bonds (actualInput C N labels)) e)

theorem actualGraph_card :
    Fintype.card (actualGraph C N labels).Edge = Fintype.card C.base.Edge+9*r := by
  change Fintype.card (Fin (bonds (actualInput C N labels)).length) = _
  rw [Fintype.card_fin]
  simp only [bonds,List.length_append,family_length,familyInput,actualInput,
    QuantumListGraph.packed,List.length_ofFn]
  rw [Fintype.card_congr labels,Fintype.card_fin]

end ContinuumCoulomb.QuantumCrossingListLayer

namespace ContinuumCoulomb.QuantumCrossingSelectProgram
open scoped Classical

variable {G : QMARationalExchangeGraph} {r k : ℕ}
    (S : QMARationalCrossingSelection G r) (labels : G.Edge ≃ Fin k)

theorem compiled_graph_coefficientBound {N : ℚ} (hN : 0 ≤ N) {m L T : ℝ}
    (hm : (Fintype.card G.Edge : ℝ) ≤ m) (hL : 1 ≤ L) (hT : |(N : ℝ)| ≤ T)
    (hc : G.CoefficientBound L) :
    (QuantumCrossingListLayer.actualGraph (computedLayer S labels) N (Equiv.refl _)).CoefficientBound
      (qmaCrossingCoefficientBound m r ((m+1)*L) T) :=
  QuantumCrossingListLayer.actualGraph_coefficientBound _ _ _
    (computedLayer_output_coefficientBound S labels hN hm hL hT hc)

theorem compiled_graph_count {m : ℝ} (hm : (Fintype.card G.Edge : ℝ) ≤ m) (N : ℚ) :
    (Fintype.card
      (QuantumCrossingListLayer.actualGraph (computedLayer S labels) N (Equiv.refl _)).Edge : ℝ)
      ≤ m+9*r := by
  rw [QuantumCrossingListLayer.actualGraph_card (computedLayer S labels) N (Equiv.refl _),
    Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat]
  have h : (Fintype.card (retainedGraph S labels).Edge : ℝ) ≤ (Fintype.card G.Edge : ℝ) := by
    exact_mod_cast retainedGraph_count S labels
  exact add_le_add (h.trans hm) (le_refl (9*(r : ℝ)))

theorem compiled_merged_coefficientBound {N : ℚ} (hN : 0 ≤ N) {m L T : ℝ}
    (hm : (Fintype.card G.Edge : ℝ) ≤ m) (hL : 1 ≤ L) (hT : |(N : ℝ)| ≤ T)
    (hc : G.CoefficientBound L) :
    (QuantumCrossingListLayer.actualGraph (computedLayer S labels) N (Equiv.refl _)).merge.CoefficientBound
      ((m+9*r+1)*qmaCrossingCoefficientBound m r ((m+1)*L) T) := by
  have hm0 : 0 ≤ m := (Nat.cast_nonneg _).trans hm
  have hL0 : 0 ≤ L := by linarith
  have henv : 1 ≤ qmaCrossingCoefficientBound m r ((m+1)*L) T := by
    unfold qmaCrossingCoefficientBound
    have hp : 0 ≤ (11*(r : ℝ)+2)*(qmaCrossingRadiusBound m r ((m+1)*L) T)^2 := by
      positivity
    have hb : 0 ≤ (m+1)*L := by positivity
    linarith
  exact QMARationalExchangeGraph.merge_coefficientBound _
    (compiled_graph_count S labels hm N) henv
    (compiled_graph_coefficientBound S labels hN hm hL hT hc)

theorem compiled_merged_nat {N : ℚ} (hN : 0 ≤ N) {m L T : ℕ}
    (hm : Fintype.card G.Edge ≤ m) (hL : 1 ≤ L) (hT : |(N : ℝ)| ≤ T)
    (hc : G.CoefficientBound L) :
    (QuantumCrossingListLayer.actualGraph (computedLayer S labels) N (Equiv.refl _)).merge.CoefficientBound
      ((m+9*r+1)*QuantumCoefficientPrograms.crossingCoefficient m r ((m+1)*L) T) := by
  have hm' : (Fintype.card G.Edge : ℝ) ≤ m := by exact_mod_cast hm
  have hL' : (1 : ℝ) ≤ L := by exact_mod_cast hL
  simpa only [Nat.cast_mul,Nat.cast_add,Nat.cast_one,Nat.cast_ofNat,
    QuantumCoefficientPrograms.crossingCoefficient_cast] using
      compiled_merged_coefficientBound S labels hN hm' hL' hT hc

end ContinuumCoulomb.QuantumCrossingSelectProgram

end

end OAI
