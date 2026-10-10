import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumCrossingPacketBounds
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumPlanarTapeSupport

namespace OAI

/-! Merging the actual bond tape reduces its length and increases each
coefficient by at most the input length. These bounds apply directly to the
numeric graph used by the final route compiler. -/

noncomputable section
namespace ContinuumCoulomb.QuantumListMerge
open MediatorListProgram

theorem value_length_le_input (n : ℕ) (xs : List Bond) :
    (value n xs).length ≤ xs.length := by
  have hs : support n xs ⊆ xs.map ordered := by
    intro p hp
    exact of_decide_eq_true (List.mem_filter.mp hp).2
  have h := (support_nodup n xs).length_le_of_subset hs
  simpa only [value,List.length_map] using h

theorem value_coefficient_bound (n : ℕ) (xs : List Bond) {L : ℝ}
    (hL : 0 ≤ L) (hw : ∀ e ∈ xs, |(e.2.2 : ℝ)| ≤ L) :
    ∀ e ∈ value n xs, |(e.2.2 : ℝ)| ≤ xs.length*L := by
  intro e he
  obtain ⟨p,_,rfl⟩ := List.mem_map.mp he
  exact weight_abs_le xs p hL hw

end ContinuumCoulomb.QuantumListMerge

namespace ContinuumCoulomb.QuantumPlanarTapeGeometry
open QuantumPlanarTapeProgram
open scoped Classical

theorem graph_count (x : Input) (hn : ∀ e ∈ x.1.1.2.1, e.1 ≠ e.2.1) :
    Fintype.card (graph x hn).Edge ≤ x.1.1.2.1.length := by
  change Fintype.card (Fin (merged x).length) ≤ _
  rw [Fintype.card_fin]
  exact QuantumListMerge.value_length_le_input _ _

theorem graph_coefficientBound (x : Input)
    (hn : ∀ e ∈ x.1.1.2.1, e.1 ≠ e.2.1) {m L : ℝ}
    (hm : (x.1.1.2.1.length : ℝ) ≤ m) (hL : 0 ≤ L)
    (hc : |(x.1.1.2.2 : ℝ)| ≤ L)
    (hw : ∀ e ∈ x.1.1.2.1, |(e.2.2 : ℝ)| ≤ L) :
    (graph x hn).CoefficientBound ((m+1)*L) := by
  have hm0 : 0 ≤ m := (Nat.cast_nonneg _).trans hm
  constructor
  · change |(x.1.1.2.2 : ℝ)| ≤ _
    nlinarith
  · intro e
    have h := QuantumListMerge.value_coefficient_bound x.1.1.1 x.1.1.2.1 hL hw
      _ (List.get_mem (merged x) e)
    change |(((merged x).get e).2.2 : ℝ)| ≤ _
    exact h.trans ((mul_le_mul_of_nonneg_right hm hL).trans (by nlinarith))

theorem graph_coefficientBound_of_raw (x : Input)
    (hb : SourceBondLists.bounded x.1.1.1 x.1.1.2.1)
    (hn : ∀ e ∈ x.1.1.2.1, e.1 ≠ e.2.1) {m L : ℝ}
    (hm : (Fintype.card (rawGraph x hb hn).Edge : ℝ) ≤ m) (hL : 0 ≤ L)
    (hc : (rawGraph x hb hn).CoefficientBound L) :
    (graph x hn).CoefficientBound ((m+1)*L) := by
  have hlen : (x.1.1.2.1.length : ℝ) ≤ m := by
    change (Fintype.card (Fin x.1.1.2.1.length) : ℝ) ≤ m at hm
    simpa only [Fintype.card_fin] using hm
  apply graph_coefficientBound x hn hlen hL hc.1
  intro e he
  obtain ⟨i,rfl⟩ := List.mem_iff_get.mp he
  exact hc.2 i

end ContinuumCoulomb.QuantumPlanarTapeGeometry

namespace ContinuumCoulomb.QuantumCrossingSelectProgram
open QuantumPlanarTapeProgram
open scoped Classical

variable {G : QMARationalExchangeGraph} {r k : ℕ}
    (S : QMARationalCrossingSelection G r) (labels : G.Edge ≃ Fin k)

theorem compiled_planar_bounds {N : ℚ} (hN : 0 ≤ N) {m L T : ℝ}
    (hm : (Fintype.card G.Edge : ℝ) ≤ m) (hL : 1 ≤ L) (hT : |(N : ℝ)| ≤ T)
    (hc : G.CoefficientBound L) (x : QuantumPlanarTapeProgram.Input)
    (hx : x.1.1 = QuantumCrossingListLayer.value
      (QuantumCrossingListLayer.actualInput (computedLayer S labels) N (Equiv.refl _)))
    (hn : ∀ e ∈ x.1.1.2.1, e.1 ≠ e.2.1) :
    (QuantumPlanarTapeGeometry.graph x hn).CoefficientBound
      ((m+9*r+1)*qmaCrossingCoefficientBound m r ((m+1)*L) T) ∧
    (Fintype.card (QuantumPlanarTapeGeometry.graph x hn).Edge : ℝ) ≤ m+9*r := by
  let E := qmaCrossingCoefficientBound m r ((m+1)*L) T
  have hm0 : 0 ≤ m := (Nat.cast_nonneg _).trans hm
  have hL0 : 0 ≤ L := by linarith
  have hE : 0 ≤ E := by
    dsimp [E,qmaCrossingCoefficientBound]
    positivity
  have hout := computedLayer_output_coefficientBound S labels hN hm hL hT hc
  have hlen : (x.1.1.2.1.length : ℝ) ≤ m+9*r := by
    rw [hx]
    change ((QuantumCrossingListLayer.bonds
      (QuantumCrossingListLayer.actualInput (computedLayer S labels) N (Equiv.refl _))).length : ℝ)
      ≤ m+9*r
    have h := compiled_graph_count S labels hm N
    change (Fintype.card (Fin (QuantumCrossingListLayer.bonds
      (QuantumCrossingListLayer.actualInput (computedLayer S labels) N (Equiv.refl _))).length) : ℝ)
      ≤ m+9*r at h
    simpa only [Fintype.card_fin] using h
  constructor
  · apply QuantumPlanarTapeGeometry.graph_coefficientBound x hn hlen hE
    · rw [hx]
      change |(QuantumCrossingListLayer.constant
        (QuantumCrossingListLayer.actualInput (computedLayer S labels) N (Equiv.refl _)) : ℝ)| ≤ E
      rw [QuantumCrossingListLayer.constant_actual (computedLayer S labels) N (Equiv.refl _)]
      exact hout.1
    · intro e he
      rw [hx] at he
      exact QuantumCrossingListLayer.actual_bonds_coefficientBound _ _ _ hout e he
  · have h : (Fintype.card (QuantumPlanarTapeGeometry.graph x hn).Edge : ℝ) ≤
        (x.1.1.2.1.length : ℝ) := by
      exact_mod_cast QuantumPlanarTapeGeometry.graph_count x hn
    exact h.trans hlen

theorem compiled_planar_nat {N : ℚ} (hN : 0 ≤ N) {m L T : ℕ}
    (hm : Fintype.card G.Edge ≤ m) (hL : 1 ≤ L) (hT : |(N : ℝ)| ≤ T)
    (hc : G.CoefficientBound L) (x : QuantumPlanarTapeProgram.Input)
    (hx : x.1.1 = QuantumCrossingListLayer.value
      (QuantumCrossingListLayer.actualInput (computedLayer S labels) N (Equiv.refl _)))
    (hn : ∀ e ∈ x.1.1.2.1, e.1 ≠ e.2.1) :
    (QuantumPlanarTapeGeometry.graph x hn).CoefficientBound
      ((m+9*r+1)*QuantumCoefficientPrograms.crossingCoefficient m r ((m+1)*L) T) ∧
    Fintype.card (QuantumPlanarTapeGeometry.graph x hn).Edge ≤ m+9*r := by
  have hm' : (Fintype.card G.Edge : ℝ) ≤ m := by exact_mod_cast hm
  have hL' : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have h := compiled_planar_bounds S labels hN hm' hL' hT hc x hx hn
  constructor
  · simpa only [Nat.cast_mul,Nat.cast_add,Nat.cast_one,Nat.cast_ofNat,
      QuantumCoefficientPrograms.crossingCoefficient_cast] using h.1
  · exact_mod_cast h.2

end ContinuumCoulomb.QuantumCrossingSelectProgram

end

end OAI
