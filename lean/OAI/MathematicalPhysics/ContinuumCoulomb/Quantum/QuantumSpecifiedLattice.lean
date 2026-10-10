import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumDefinedRealization
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumGraphCoefficientBound
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumCrossingPlanarRoutes
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumCrossingSize
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumLatticeSource

namespace OAI

/-! A specified finite square-lattice source, with its exact energy shift and
coefficient envelope. All estimates refer to this same constructed graph. -/

noncomputable section
namespace ContinuumCoulomb
open scoped Classical

namespace QMARationalExchangeGraph
variable (G : QMARationalExchangeGraph)

theorem merge_adjacent (position : Fin G.n → ℕ × ℕ)
    (h : ∀ e, qmaSquareGrid.Adj (position (G.left e)) (position (G.right e)))
    (e : G.merge.Edge) :
    qmaSquareGrid.Adj (position (G.merge.left e)) (position (G.merge.right e)) := by
  obtain ⟨f,he|he⟩ := G.merge_edge_source e
  · rw [he.1,he.2]
    exact h f
  · rw [he.1,he.2]
    exact (h f).symm

end QMARationalExchangeGraph

namespace QMAEvenRouteData
variable {G : QMARationalExchangeGraph} (P : QMAEvenRouteData G)

theorem output_coefficientBound {N : ℚ} (hN : 0 ≤ N) {m L T : ℝ}
    (hm : (Fintype.card G.Edge:ℝ) ≤ m) (hL : 1 ≤ L) (hT : |(N:ℝ)| ≤ T)
    (hc : G.CoefficientBound L) (D : ℕ) :
    (P.output N D).CoefficientBound
      (qmaPathIteratedBound (3*m) (qmaPathCoefficientBound m L T) T D) := by
  have hm0 : 0 ≤ m := (Nat.cast_nonneg _).trans hm
  have hcount : (Fintype.card (P.schedule N).graph.Edge:ℝ) ≤ 3*m := by
    have hs : Fintype.card (P.schedule N).graph.Edge ≤ 3*Fintype.card G.Edge := by
      change Fintype.card (G.subdivide Finset.univ (fun _ => true) N).Edge ≤ _
      rw [G.subdivide_edge_count]
      simp only [Finset.card_univ]
      omega
    have hs' : (Fintype.card (P.schedule N).graph.Edge:ℝ) ≤
        3*(Fintype.card G.Edge:ℝ) := by exact_mod_cast hs
    exact hs'.trans (by linarith)
  exact (P.schedule N).iterate_coefficientBound hN hcount
    (qmaPathCoefficientBound_one hm0 hL) hT
    (G.subdivide_coefficientBound Finset.univ (fun _ => true) hN hm hL hT hc) D

end QMAEvenRouteData

namespace QMAPortRouteData
variable {G : QMARationalExchangeGraph} (P : QMAPortRouteData G)
variable (N : ℚ) {D : ℕ} (hD : ∀ e, P.length e ≤ D)
variable (havoid : ∀ i : P.Interior, ∀ v, P.cell i ≠ P.position v)
variable (hpositive : ∀ v, 0 < (P.position v).1 ∧ 0 < (P.position v).2)

def latticeGraph : QMARationalExchangeGraph :=
  ((P.crossingPlanarRoute N hD havoid hpositive).toEven.output N 80).merge

def latticePosition := (P.crossingPlanarRoute N hD havoid hpositive).toEven.outputPosition N 80

theorem lattice_vertices_ge : G.n ≤ (P.latticeGraph N hD havoid hpositive).n := by
  have h := (P.crossingPlanarRoute N hD havoid hpositive).toEven.output_vertices_ge N 80
  have hfirst := P.schedule.iterate_vertices_ge N D
  change G.n ≤ _ at hfirst
  change (P.crossingOutput N hD).n ≤ _ at h
  change G.n ≤ _
  have hc : (P.finishedGraph N D).n ≤ (P.crossingOutput N hD).n := by
    change (P.finishedGraph N D).n ≤ (P.finishedGraph N D).n+P.crossingCells.card*2
    omega
  exact hfirst.trans (hc.trans h)

theorem lattice_position_injective :
    Function.Injective (P.latticePosition N hD havoid hpositive) :=
  (P.crossingPlanarRoute N hD havoid hpositive).toEven.output_position_injective N 80

theorem lattice_adjacent (e : (P.latticeGraph N hD havoid hpositive).Edge) :
    qmaSquareGrid.Adj
      (P.latticePosition N hD havoid hpositive ((P.latticeGraph N hD havoid hpositive).left e))
      (P.latticePosition N hD havoid hpositive ((P.latticeGraph N hD havoid hpositive).right e)) := by
  let R := P.crossingPlanarRoute N hD havoid hpositive
  have hw : ∀ e, R.toEven.work e ≤ 80 := by
    intro e
    have hl := P.crossingPlanarRoute_length N hD havoid hpositive e
    change R.length e ≤ 20 at hl
    change 4*R.length e-1 ≤ 80
    omega
  exact (R.toEven.output N 80).merge_adjacent _ (R.toEven.output_adjacent N hw) e

theorem lattice_bounded {X Y : ℕ}
    (hsource : ∀ v, (P.position v).1 < X ∧ (P.position v).2 < Y)
    (hpath : ∀ e k, k ≤ P.length e → (P.point e k).1 < X ∧ (P.point e k).2 < Y) :
    ∀ v, (P.latticePosition N hD havoid hpositive v).1 < 256*X ∧
      (P.latticePosition N hD havoid hpositive v).2 < 256*Y := by
  have hb := P.crossingPlanarRoute_bounded N hD havoid hpositive hsource hpath
  have h := (P.crossingPlanarRoute N hD havoid hpositive).toEven.output_position_bounded
    N 80 ((P.crossingPlanarRoute N hD havoid hpositive).toEven_bounded hb)
  simpa only [latticePosition,← Nat.mul_assoc] using h

theorem lattice_energy_error (hN : 0 < N) :
    |(P.latticeGraph N hD havoid hpositive).energy-G.energy| ≤ ((D+82:ℕ):ℝ)/(N:ℝ) := by
  let R := P.crossingPlanarRoute N hD havoid hpositive
  have he := R.toEven.output_energy_error hN 80
  have hc := P.mergedOutput_energy_error hN hD
  rw [latticeGraph,QMARationalExchangeGraph.merge_energy]
  calc
    _ ≤ |(R.toEven.output N 80).energy-(P.crossingOutput N hD).merge.energy|+
        |(P.crossingOutput N hD).merge.energy-G.energy| := abs_sub_le _ _ _
    _ ≤ ((80+1:ℕ):ℝ)/(N:ℝ)+((D+1:ℕ):ℝ)/(N:ℝ) := add_le_add he hc
    _ = _ := by push_cast; ring

def latticeSource (hn : 0 < G.n) (a b : ℚ) (hab : a < b) : SquareLatticeHeisenberg :=
  (P.latticeGraph N hD havoid hpositive).latticeSource
    (hn.trans_le (P.lattice_vertices_ge N hD havoid hpositive))
    (P.latticePosition N hD havoid hpositive)
    (P.lattice_position_injective N hD havoid hpositive)
    (P.lattice_adjacent N hD havoid hpositive)
    (QMARationalExchangeGraph.merge_simple _) a b hab

theorem latticeSource_energy (hn : 0 < G.n) (a b : ℚ) (hab : a < b) :
    realSourceGroundEnergy (P.latticeSource N hD havoid hpositive hn a b hab) =
      (P.latticeGraph N hD havoid hpositive).energy-
        ((P.latticeGraph N hD havoid hpositive).constant:ℝ) :=
  QMARationalExchangeGraph.latticeSource_energy _ _ _ _ _ _ _ _ _

end QMAPortRouteData
end ContinuumCoulomb

end

end OAI
