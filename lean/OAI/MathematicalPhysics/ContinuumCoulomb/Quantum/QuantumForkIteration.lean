import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumForkStateAccuracy
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumForkRounds

namespace OAI

/-! Iterating the actual weighted graph keeps a proved full-space energy error. -/

noncomputable section
namespace ContinuumCoulomb
open MediatorGraph
open scoped BigOperators Classical

structure QMAWeightedForkNetwork (c : ℕ) where
  graph : QMAForkNetwork c
  weight : graph.Edge → ℝ
  active : (Σ i, Fin (graph.degree i)) → ℝ
  constant : ℝ

namespace QMAWeightedForkNetwork
variable {c : ℕ}

def energy (G : QMAWeightedForkNetwork c) : ℝ :=
  sourceMatrixBottom G.graph.n (G.graph.state.matrix G.weight G.active G.constant)

def scale (G : QMAWeightedForkNetwork c) (N : ℝ) : ℝ :=
  let P := G.graph.state
  let B := 3*(∑ a, |P.retainedWeight G.weight G.active a|)+|G.constant|
  let A := 3*∑ e, (1+2*|P.pairWeight G.active 0 e|+2*|P.pairWeight G.active 1 e|)
  let D := B+12*∑ e, (1+|P.pairWeight G.active 0 e|+|P.pairWeight G.active 1 e|)^2
  qmaRoutingScale A D N

def next (G : QMAWeightedForkNetwork c) (N : ℝ) : QMAWeightedForkNetwork c where
  graph := G.graph.next
  weight := G.graph.state.nextWeight (G.scale N) G.weight G.active
  active := G.graph.state.nextActive (G.scale N) G.active
  constant := G.graph.state.nextConstant (G.scale N) G.constant G.active

theorem next_energy_error (G : QMAWeightedForkNetwork c) {N : ℝ} (hN : 0 < N) :
    |(G.next N).energy-G.energy| ≤ 1/N := by
  exact G.graph.state.next_accuracy G.weight G.active G.constant hN

def iterate (G : QMAWeightedForkNetwork c) (N : ℝ) : ℕ → QMAWeightedForkNetwork c
  | 0 => G
  | k+1 => (G.iterate N k).next N

theorem iterate_graph (G : QMAWeightedForkNetwork c) (N : ℝ) (k : ℕ) :
    (G.iterate N k).graph = G.graph.iterate k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change (G.iterate N k).graph.next = (G.graph.iterate k).next
    rw [ih]

theorem iterate_energy_error (G : QMAWeightedForkNetwork c) {N : ℝ} (hN : 0 < N) (k : ℕ) :
    |(G.iterate N k).energy-G.energy| ≤ (k:ℝ)/N := by
  induction k with
  | zero => simp [iterate]
  | succ k ih =>
    change |((G.iterate N k).next N).energy-G.energy| ≤ ((k+1:ℕ):ℝ)/N
    calc
      _ ≤ |((G.iterate N k).next N).energy-(G.iterate N k).energy| +
          |(G.iterate N k).energy-G.energy| := abs_sub_le _ _ _
      _ ≤ 1/N+(k:ℝ)/N := add_le_add ((G.iterate N k).next_energy_error hN) ih
      _ = ((k+1:ℕ):ℝ)/N := by push_cast; ring

end QMAWeightedForkNetwork
end ContinuumCoulomb

end

end OAI
