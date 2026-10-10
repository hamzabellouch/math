import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumCrossingCompiled
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumGraphCoefficientBound
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumCoefficientPrograms

namespace OAI

/-! Polynomial coefficient bounds for the literal endpoint scan, including
its retained background, selected couplings and merged output. -/

noncomputable section
namespace ContinuumCoulomb.QuantumCrossingSelectProgram
open MediatorListProgram
open scoped Classical

theorem weight_abs_le (xs : List Bond) (p : QuantumRouteCode.Pair) {L : ℝ}
    (hL : 0 ≤ L) (h : ∀ e ∈ xs, |(e.2.2 : ℝ)| ≤ L) :
    |(weight (xs,p) : ℝ)| ≤ xs.length*L := by
  induction xs with
  | nil => simp [weight]
  | cons e xs ih =>
    have he := h e List.mem_cons_self
    have ht := ih (fun b hb => h b (List.mem_cons_of_mem _ hb))
    have hc : |(contribution (e,p) : ℝ)| ≤ L := by
      unfold contribution
      split_ifs
      · exact he
      · simpa only [Rat.cast_zero,abs_zero] using hL
    change |((contribution (e,p)+weight (xs,p) : ℚ) : ℝ)| ≤ _
    rw [Rat.cast_add]
    have ha := abs_add_le (contribution (e,p) : ℝ) (weight (xs,p) : ℝ)
    simp only [List.length_cons,Nat.cast_add,Nat.cast_one]
    nlinarith

variable {G : QMARationalExchangeGraph} {r k : ℕ}
    (S : QMARationalCrossingSelection G r) (labels : G.Edge ≃ Fin k)

theorem packed_weight_bound {L : ℝ} (hc : G.CoefficientBound L) :
    ∀ e ∈ QuantumListGraph.packed G labels, |(e.2.2 : ℝ)| ≤ L := by
  intro e he
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp he
  exact hc.2 (labels.symm i)

theorem retainedGraph_count : Fintype.card (retainedGraph S labels).Edge ≤ Fintype.card G.Edge := by
  change Fintype.card (Fin
    (retained (pairs (List.ofFn (encodedSites S.site)),QuantumListGraph.packed G labels)).length) ≤ _
  rw [Fintype.card_fin,Fintype.card_congr labels,Fintype.card_fin]
  simpa only [retained,QuantumListGraph.packed,List.length_ofFn] using
    (List.length_filter_le (fun e => keep (pairs (List.ofFn (encodedSites S.site)),e))
      (QuantumListGraph.packed G labels))

theorem retainedGraph_coefficientBound {L : ℝ} (hc : G.CoefficientBound L) :
    (retainedGraph S labels).CoefficientBound L := by
  refine ⟨hc.1,?_⟩
  intro e
  apply packed_weight_bound labels hc
  exact ((retained_mem _ _).mp
    (List.get_mem (retained (pairs (List.ofFn (encodedSites S.site)),
      QuantumListGraph.packed G labels)) e)).1

theorem computed_coupling_bound {m L : ℝ}
    (hm : (Fintype.card G.Edge : ℝ) ≤ m) (hL : 0 ≤ L) (hc : G.CoefficientBound L)
    (i : Fin r) (a : Fin 2) :
    |(weight (QuantumListGraph.packed G labels,terminalPair a (encodedSites S.site i)) : ℝ)| ≤ m*L := by
  have hk : ((QuantumListGraph.packed G labels).length : ℝ) ≤ m := by
    have hk' : k = Fintype.card G.Edge :=
      ((Fintype.card_congr labels).trans (Fintype.card_fin k)).symm
    simpa only [QuantumListGraph.packed,List.length_ofFn,hk'] using hm
  exact (weight_abs_le _ _ hL (packed_weight_bound labels hc)).trans
    (mul_le_mul_of_nonneg_right hk hL)

theorem computedLayer_output_coefficientBound {N : ℚ} (hN : 0 ≤ N) {m L T : ℝ}
    (hm : (Fintype.card G.Edge : ℝ) ≤ m) (hL : 1 ≤ L) (hT : |(N : ℝ)| ≤ T)
    (hc : G.CoefficientBound L) :
    ((computedLayer S labels).output N).CoefficientBound
      (qmaCrossingCoefficientBound m r ((m+1)*L) T) := by
  have hm0 : 0 ≤ m := (Nat.cast_nonneg _).trans hm
  have hL0 : 0 ≤ L := by linarith
  have hLL : L ≤ (m+1)*L := by nlinarith
  have hcount : (Fintype.card (computedLayer S labels).base.Edge : ℝ) ≤ m := by
    exact (show (Fintype.card (retainedGraph S labels).Edge : ℝ) ≤
      (Fintype.card G.Edge : ℝ) by exact_mod_cast retainedGraph_count S labels).trans hm
  have hbase : (computedLayer S labels).base.CoefficientBound ((m+1)*L) := by
    have h := retainedGraph_coefficientBound S labels hc
    exact ⟨h.1.trans hLL,fun e => (h.2 e).trans hLL⟩
  apply (computedLayer S labels).output_coefficientBound hN hcount (hL.trans hLL) hT hbase
  · intro i
    exact (computed_coupling_bound S labels hm hL0 hc i 0).trans (by nlinarith)
  · intro i
    exact (computed_coupling_bound S labels hm hL0 hc i 1).trans (by nlinarith)

theorem computedLayer_output_count {m : ℝ} (hm : (Fintype.card G.Edge : ℝ) ≤ m) (N : ℚ) :
    (Fintype.card ((computedLayer S labels).output N).Edge : ℝ) ≤ m+9*r := by
  rw [(computedLayer S labels).output_edge_count,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat]
  have h : (Fintype.card (retainedGraph S labels).Edge : ℝ) ≤ (Fintype.card G.Edge : ℝ) := by
    exact_mod_cast retainedGraph_count S labels
  exact add_le_add (h.trans hm) (le_refl (9*(r : ℝ)))

theorem computedLayer_merged_coefficientBound {N : ℚ} (hN : 0 ≤ N) {m L T : ℝ}
    (hm : (Fintype.card G.Edge : ℝ) ≤ m) (hL : 1 ≤ L) (hT : |(N : ℝ)| ≤ T)
    (hc : G.CoefficientBound L) :
    ((computedLayer S labels).output N).merge.CoefficientBound
      ((m+9*r+1)*qmaCrossingCoefficientBound m r ((m+1)*L) T) := by
  have hm0 : 0 ≤ m := (Nat.cast_nonneg _).trans hm
  have hL0 : 0 ≤ L := by linarith
  have henv : 1 ≤ qmaCrossingCoefficientBound m r ((m+1)*L) T := by
    unfold qmaCrossingCoefficientBound
    have hmul : 0 ≤ (11*(r : ℝ)+2)*
        (qmaCrossingRadiusBound m r ((m+1)*L) T)^2 := by positivity
    have hbase : 0 ≤ (m+1)*L := by positivity
    linarith
  exact (((computedLayer S labels).output N).merge_coefficientBound
    (computedLayer_output_count S labels hm N) henv
    (computedLayer_output_coefficientBound S labels hN hm hL hT hc))

theorem computedLayer_output_nat {N : ℚ} (hN : 0 ≤ N) {m L T : ℕ}
    (hm : Fintype.card G.Edge ≤ m) (hL : 1 ≤ L) (hT : |(N : ℝ)| ≤ T)
    (hc : G.CoefficientBound L) :
    ((computedLayer S labels).output N).CoefficientBound
      (QuantumCoefficientPrograms.crossingCoefficient m r ((m+1)*L) T) := by
  have hm' : (Fintype.card G.Edge : ℝ) ≤ m := by exact_mod_cast hm
  have hL' : (1 : ℝ) ≤ L := by exact_mod_cast hL
  simpa only [QuantumCoefficientPrograms.crossingCoefficient_cast,Nat.cast_mul,
    Nat.cast_add,Nat.cast_one] using
      computedLayer_output_coefficientBound S labels hN hm' hL' hT hc

end ContinuumCoulomb.QuantumCrossingSelectProgram

end

end OAI
