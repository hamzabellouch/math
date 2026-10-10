import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumSpecifiedLattice
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumCoefficientPrograms

namespace OAI

/-! The specified physical lattice has a polynomial coefficient envelope,
including both crossing offsets and the final merge of parallel edges. -/

noncomputable section
namespace ContinuumCoulomb
open scoped Classical

namespace QMAEvenRouteData
variable {G : QMARationalExchangeGraph} (P : QMAEvenRouteData G)

theorem output_edge_count (N : ℚ) (D : ℕ) :
    Fintype.card (P.output N D).Edge ≤ 3^(D+1)*Fintype.card G.Edge := by
  have h := (P.schedule N).iterate_edge_count N D
  have hs : Fintype.card (P.schedule N).graph.Edge ≤ 3*Fintype.card G.Edge := by
    change Fintype.card (G.subdivide Finset.univ (fun _ => true) N).Edge ≤ _
    rw [G.subdivide_edge_count]
    simp only [Finset.card_univ]
    omega
  exact h.trans (by simpa [pow_succ,Nat.mul_assoc] using Nat.mul_le_mul_left (3^D) hs)

end QMAEvenRouteData

namespace QuantumCoefficientPrograms

def latticeBound (D m r L T : ℕ) : ℕ :=
  let m₁ := 3^D*m
  let L₁ := iterated m L T D
  let m₂ := m₁+9*r
  let L₂ := crossingCoefficient m₁ r ((m₁+1)*L₁) T
  let L₃ := (m₂+1)*L₂
  let L₄ := iterated (3*m₂) (pathCoefficient m₂ L₃ T) T 80
  (3^81*m₂+1)*L₄

theorem pathCoefficient_one (m L T : ℕ) : 1 ≤ pathCoefficient m L T := by
  unfold pathCoefficient
  omega

theorem crossingCoefficient_one (m r L T : ℕ) : 1 ≤ crossingCoefficient m r L T := by
  unfold crossingCoefficient
  omega

theorem iterated_one {L : ℕ} (hL : 1 ≤ L) (m T D : ℕ) : 1 ≤ iterated m L T D := by
  cases D
  · exact hL
  · exact pathCoefficient_one _ _ _

end QuantumCoefficientPrograms

namespace QMAPortRouteData
variable {G : QMARationalExchangeGraph} (P : QMAPortRouteData G)

 theorem lattice_coefficientBound {N : ℚ} (hN : 0 ≤ N) {D : ℕ}
    (hD : ∀ e, P.length e ≤ D)
    (havoid : ∀ i : P.Interior, ∀ v, P.cell i ≠ P.position v)
    (hpositive : ∀ v, 0 < (P.position v).1 ∧ 0 < (P.position v).2)
    {L T : ℕ} (hL : 1 ≤ L) (hT : |(N:ℝ)| ≤ T) (hc : G.CoefficientBound L) :
    (P.latticeGraph N hD havoid hpositive).CoefficientBound
      (QuantumCoefficientPrograms.latticeBound D (Fintype.card G.Edge) P.crossingCells.card L T) := by
  let m := Fintype.card G.Edge
  let r := P.crossingCells.card
  let m₁ := 3^D*m
  let L₁ := QuantumCoefficientPrograms.iterated m L T D
  let m₂ := m₁+9*r
  let L₂ := QuantumCoefficientPrograms.crossingCoefficient m₁ r ((m₁+1)*L₁) T
  let L₃ := (m₂+1)*L₂
  let L₄ := QuantumCoefficientPrograms.iterated (3*m₂)
    (QuantumCoefficientPrograms.pathCoefficient m₂ L₃ T) T 80
  have hLr : (1:ℝ) ≤ L := by exact_mod_cast hL
  have hL₁n : 1 ≤ L₁ := QuantumCoefficientPrograms.iterated_one hL m T D
  have hL₁ : (1:ℝ) ≤ L₁ := by exact_mod_cast hL₁n
  have hm₁ : (Fintype.card (P.finishedGraph N D).Edge:ℝ) ≤ m₁ := by
    exact_mod_cast P.schedule.iterate_edge_count N D
  have hc₁ : (P.finishedGraph N D).CoefficientBound (L₁:ℝ) := by
    simpa only [L₁,QuantumCoefficientPrograms.iterated_cast] using
      P.schedule.iterate_coefficientBound hN (le_refl (m:ℝ)) hLr hT hc D
  have hc₂ : (P.crossingOutput N hD).CoefficientBound (L₂:ℝ) := by
    simpa only [L₂,QuantumCoefficientPrograms.crossingCoefficient_cast,Nat.cast_mul,Nat.cast_add,
      Nat.cast_one,QuantumCoefficientPrograms.iterated_cast] using
      (P.portCrossingSelection N hD).output_coefficientBound hN hm₁ hL₁ hT hc₁
  have hm₂n : Fintype.card (P.crossingOutput N hD).Edge ≤ m₂ := by
    have he := (P.portCrossingSelection N hD).layer.output_edge_count N
    have hr : Fintype.card (P.portCrossingSelection N hD).retained.Edge ≤
        Fintype.card (P.finishedGraph N D).Edge := Fintype.card_subtype_le _
    have hcount := P.schedule.iterate_edge_count N D
    change Fintype.card (P.finishedGraph N D).Edge ≤ m₁ at hcount
    change Fintype.card (P.crossingOutput N hD).Edge =
      Fintype.card (P.portCrossingSelection N hD).retained.Edge+9*r at he
    change Fintype.card (P.crossingOutput N hD).Edge ≤ m₁+9*r
    omega
  have hm₂ : (Fintype.card (P.crossingOutput N hD).Edge:ℝ) ≤ m₂ := by exact_mod_cast hm₂n
  have hL₂n : 1 ≤ L₂ := QuantumCoefficientPrograms.crossingCoefficient_one _ _ _ _
  have hL₂ : (1:ℝ) ≤ L₂ := by exact_mod_cast hL₂n
  have hL₃n : 1 ≤ L₃ := by dsimp [L₃]; nlinarith
  have hL₃ : (1:ℝ) ≤ L₃ := by exact_mod_cast hL₃n
  have hc₃ : (P.crossingOutput N hD).merge.CoefficientBound (L₃:ℝ) := by
    simpa only [L₃,Nat.cast_mul,Nat.cast_add,Nat.cast_one] using
      (P.crossingOutput N hD).merge_coefficientBound hm₂ hL₂ hc₂
  have hm₃n : Fintype.card (P.crossingOutput N hD).merge.Edge ≤ m₂ :=
    (P.crossingOutput N hD).merge_edge_count.trans hm₂n
  have hm₃ : (Fintype.card (P.crossingOutput N hD).merge.Edge:ℝ) ≤ m₂ := by exact_mod_cast hm₃n
  let R := (P.crossingPlanarRoute N hD havoid hpositive).toEven
  have hc₄ : (R.output N 80).CoefficientBound (L₄:ℝ) := by
    simpa only [L₄,QuantumCoefficientPrograms.iterated_cast,
      QuantumCoefficientPrograms.pathCoefficient_cast,Nat.cast_mul,Nat.cast_ofNat] using
      R.output_coefficientBound hN hm₃ hL₃ hT hc₃ 80
  have hm₄n : Fintype.card (R.output N 80).Edge ≤ 3^81*m₂ :=
    (R.output_edge_count N 80).trans (Nat.mul_le_mul_left _ hm₃n)
  have hm₄ : (Fintype.card (R.output N 80).Edge:ℝ) ≤ (3^81*m₂:ℕ) := by exact_mod_cast hm₄n
  have hL₄n : 1 ≤ L₄ := QuantumCoefficientPrograms.iterated_one
    (QuantumCoefficientPrograms.pathCoefficient_one _ _ _) _ _ _
  have hL₄ : (1:ℝ) ≤ L₄ := by exact_mod_cast hL₄n
  simpa only [latticeGraph,QuantumCoefficientPrograms.latticeBound, L₄,L₃,L₂,m₂,m₁,L₁,m,r,
    Nat.cast_mul,Nat.cast_add,Nat.cast_one] using
    (R.output N 80).merge_coefficientBound hm₄ hL₄ hc₄

end QMAPortRouteData
end ContinuumCoulomb

end

end OAI
