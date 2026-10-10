import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumCrossingCoefficientBound
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumCrossingSelection
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumMergeEdges

namespace OAI

/-! Summing parallel edges or selecting the two interactions of a crossing
preserves polynomial coefficient bounds. -/

noncomputable section
namespace ContinuumCoulomb
open scoped BigOperators Classical

namespace QMARationalExchangeGraph
variable (G : QMARationalExchangeGraph)

theorem merge_coefficientBound {m L : ℝ} (hm : (Fintype.card G.Edge:ℝ) ≤ m)
    (hL : 1 ≤ L) (hc : G.CoefficientBound L) :
    G.merge.CoefficientBound ((m+1)*L) := by
  have hm0 : 0 ≤ m := (Nat.cast_nonneg _).trans hm
  have hL0 : 0 ≤ L := by linarith
  constructor
  · change |(G.constant:ℝ)| ≤ _
    nlinarith [hc.1]
  · intro p
    dsimp only [merge]
    push_cast
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc
      _ ≤ ∑ _e : G.Edge, L := Finset.sum_le_sum (fun e _ => by
        split_ifs
        · exact hc.2 e
        · simpa using hL0)
      _ = (Fintype.card G.Edge:ℝ)*L := by simp
      _ ≤ m*L := mul_le_mul_of_nonneg_right hm hL0
      _ ≤ (m+1)*L := by nlinarith

end QMARationalExchangeGraph

namespace QMARationalCrossingSelection
variable {G : QMARationalExchangeGraph} {r : ℕ} (S : QMARationalCrossingSelection G r)

theorem weight_abs_bound {m L : ℝ} (hm : (Fintype.card G.Edge:ℝ) ≤ m)
    (hL : 1 ≤ L) (hc : G.CoefficientBound L) (p : Fin r × Fin 2) :
    |(S.weight p:ℝ)| ≤ m*L := by
  have hL0 : 0 ≤ L := by linarith
  have hcard : (Fintype.card {e : G.Edge // S.tag e = some p}:ℝ) ≤
      (Fintype.card G.Edge:ℝ) := by exact_mod_cast Fintype.card_subtype_le (fun e => S.tag e = some p)
  unfold weight
  push_cast
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc
    _ ≤ ∑ _e : {e : G.Edge // S.tag e = some p}, L := Finset.sum_le_sum (fun e _ => hc.2 e.val)
    _ = (Fintype.card {e : G.Edge // S.tag e = some p}:ℝ)*L := by simp
    _ ≤ m*L := mul_le_mul_of_nonneg_right (hcard.trans hm) hL0

theorem output_coefficientBound {N : ℚ} (hN : 0 ≤ N) {m L T : ℝ}
    (hm : (Fintype.card G.Edge:ℝ) ≤ m) (hL : 1 ≤ L) (hT : |(N:ℝ)| ≤ T)
    (hc : G.CoefficientBound L) :
    (S.layer.output N).CoefficientBound (qmaCrossingCoefficientBound m r ((m+1)*L) T) := by
  have hm0 : 0 ≤ m := (Nat.cast_nonneg _).trans hm
  have hL0 : 0 ≤ L := by linarith
  have hLL : L ≤ (m+1)*L := by nlinarith
  have hcount : (Fintype.card S.layer.base.Edge:ℝ) ≤ m := by
    have h : Fintype.card S.layer.base.Edge ≤ Fintype.card G.Edge := Fintype.card_subtype_le _
    have h' : (Fintype.card S.layer.base.Edge:ℝ) ≤ (Fintype.card G.Edge:ℝ) := by exact_mod_cast h
    exact h'.trans hm
  have hbase : S.layer.base.CoefficientBound ((m+1)*L) :=
    ⟨hc.1.trans hLL,fun e => (hc.2 e.val).trans hLL⟩
  apply S.layer.output_coefficientBound hN hcount (hL.trans hLL) hT hbase
  · intro i
    exact (S.weight_abs_bound hm hL hc (i,0)).trans (by nlinarith)
  · intro i
    exact (S.weight_abs_bound hm hL hc (i,1)).trans (by nlinarith)

end QMARationalCrossingSelection
end ContinuumCoulomb

end

end OAI
