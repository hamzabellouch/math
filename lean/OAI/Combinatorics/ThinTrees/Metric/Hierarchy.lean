import Mathlib
import OAI.Combinatorics.ThinTrees.Metric.CenteredMatrices
import OAI.Combinatorics.ThinTrees.Metric.CompactDuality

namespace OAI

/-! Metric hierarchy. -/

section

namespace AlgorithmicThinTrees.MetricTests
noncomputable section
open Matrix Finset StrongThinTree StrongThinTree.MultiGraph
open scoped Classical MatrixOrder

variable {n m : ℕ}

def resistance (G : MultiGraph n m) (D : Matrix (Fin n) (Fin n) ℝ) (e : Fin m) : ℝ :=
  qform (inverseOnZeroSum D) (G.incidence e)

def boundaryResistance (G : MultiGraph n m) (H : Hierarchy n)
    (D : Matrix (Fin n) (Fin n) ℝ) (A : Finset (Fin n)) : ℝ :=
  ((H.parentBoundary G A).card : ℝ)⁻¹ * ∑e ∈ H.parentBoundary G A, resistance G D e

lemma incidence_sum (G : MultiGraph n m) (e : Fin m) : ∑i, G.incidence e i=0 :=
  (mem_zeroSumSpace _).mp (G.incidence_zeroSum e)

lemma connected_of_edgeConnected {G : MultiGraph n m} {q : ℕ}
    (hq : 0 < q) (hc : G.EdgeConnected q) : G.Connected univ := by
  intro S hS hS'
  exact card_pos.mp (hq.trans_le (hc S hS hS'))

theorem metric_hierarchy_bound :
    ∃h0 : ℕ, 2 ≤ h0 ∧ ∀h : ℕ, h0 ≤ h →
      ∀(n m : ℕ) (G : MultiGraph n m) (H : Hierarchy n), 2 ≤ n →
      H.LocallyConnectedReal G h →
      ∀M : Finset (Finset (Fin n)), M ⊆ H.nodes →
      (∀A ∈ M, A ≠ univ) →
      (∀A ∈ M, ((G.cut univ A).card : ℝ)/h ≤ (H.parentBoundary G A).card) →
      ∃D : Matrix (Fin n) (Fin n) ℝ, CenteredPositive D ∧
        (∀Z : Matrix (Fin n) (Fin n) ℝ, CenteredTest Z → (D*Z).trace ≤ (G.laplacian univ*Z).trace) ∧
        (∀A ∈ M, boundaryResistance G H D A ≤ (h:ℝ)^(-31/40:ℝ)) := by
  obtain ⟨h0,hh0,hbound⟩ := polynomial_nuclear_bound
  refine ⟨h0,hh0,?_⟩
  intro h hh n m G H hn hconn M hM hroot hratio
  have hn' : 0 < n := by omega
  have hh' : 0 < h := by omega
  have hhp : (0:ℝ) < h := Nat.cast_pos.mpr hh'
  let B := regularize (G.laplacian univ)
  have hB : B.PosDef := laplacian_regularize_pd G hn'
    (connected_of_edgeConnected hh' (Hierarchy.edgeConnected_of_locally hconn))
  let K : ℝ := (h:ℝ)^(-31/40:ℝ)/2
  have hK : 0 < K := div_pos (Real.rpow_pos_of_pos hhp _) (by norm_num)
  have hb : ∀Z : Matrix (Fin n) (Fin n) ℝ, Test Z →
      ∀lam : M → ℝ, (∀A, 0 ≤ lam A) → (∑A, lam A)=1 →
      (CFC.sqrt (CFC.sqrt Z*ShortcutDual.objectiveMatrix G.incidence
        (fun A : M => H.parentBoundary G A) lam*CFC.sqrt Z)).trace^2 ≤ K*(B*Z).trace := by
    intro Z hZ lam hlam hsum
    have hle : (G.laplacian univ*Z).trace ≤ (B*Z).trace := by
      dsimp [B,regularize]
      rw [add_mul,trace_add]
      exact le_add_of_nonneg_right (trace_pairing_nonneg constantProjection_psd hZ.1)
    exact (hbound h hh n m G H hconn M hM hroot hratio Z hZ lam hlam hsum).trans
      (mul_le_mul_of_nonneg_left hle hK.le)
  obtain ⟨D,hD,havg,htr⟩ := metric_shortcut_of_trace_bound hn' G.incidence
    (fun A : M => H.parentBoundary G A) B hB hK hb
  refine ⟨centered D,centered_positive hn' hD,?_,?_⟩
  · intro Z hZ
    rw [centered_trace D hZ]
    have hh := htr Z hZ.1
    rwa [regularize_trace (G.laplacian univ) hZ] at hh
  · intro A hA
    have hc : boundaryResistance G H (centered D) A ≤
        ShortcutDual.boundaryAverage G.incidence (fun A : M => H.parentBoundary G A) ⟨A,hA⟩ D := by
      unfold boundaryResistance ShortcutDual.boundaryAverage
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (Nat.cast_nonneg _))
      exact sum_le_sum (fun e _ => inverse_centered_le hn' hD (incidence_sum G e))
    have ht : 2*K=(h:ℝ)^(-31/40:ℝ) := by dsimp [K]; ring
    exact ht ▸ hc.trans (havg ⟨A,hA⟩)

end
end AlgorithmicThinTrees.MetricTests
end

end OAI
