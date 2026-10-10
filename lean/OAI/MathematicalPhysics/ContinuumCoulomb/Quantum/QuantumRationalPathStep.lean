import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumPartialPaths
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumPathProgram

namespace OAI

/-! Exact rational graph data for a selected path-subdivision layer. -/

noncomputable section
namespace ContinuumCoulomb
open MediatorGraph
open scoped BigOperators Classical

structure QMARationalExchangeGraph where
  n : ℕ
  Edge : Type
  [edgeFinite : Fintype Edge]
  left : Edge → Fin n
  right : Edge → Fin n
  distinct : ∀ e, left e ≠ right e
  weight : Edge → ℚ
  constant : ℚ

attribute [instance] QMARationalExchangeGraph.edgeFinite

namespace QMARationalExchangeGraph

def energy (G : QMARationalExchangeGraph) : ℝ :=
  sourceMatrixBottom G.n (qmaExchangeMatrix G.left G.right (fun e => G.weight e) G.constant)

def pathScale (G : QMARationalExchangeGraph) (s : Finset G.Edge) (N : ℚ) : ℚ :=
  let B := 3*(∑ e : {e // e ∉ s}, |G.weight e.val|)+|G.constant|
  let A := 3*∑ i : Fin s.card, (1+2*|G.weight (qmaSelectedIndex s i)|)
  let D := B+4*∑ i : Fin s.card, (1+|G.weight (qmaSelectedIndex s i)|)^2
  16*(A+D+1)^3*N+4*(A+D+1)+1

theorem pathScale_cast (G : QMARationalExchangeGraph) (s : Finset G.Edge) (N : ℚ) :
    (G.pathScale s N : ℝ) = qmaPartialPathsScale (fun e => (G.weight e:ℝ)) G.constant s N := by
  simp only [pathScale,qmaPartialPathsScale,qmaRoutingScale]
  push_cast
  rfl

def subdivide (G : QMARationalExchangeGraph) (s : Finset G.Edge)
    (even : Fin s.card → Bool) (N : ℚ) : QMARationalExchangeGraph where
  n := G.n+s.card*2
  Edge := QMAPartialPathsEdge s
  left := qmaPartialPathsLeft G.left G.right s
  right := qmaPartialPathsRight G.right s even
  distinct := qmaPartialPaths_distinct G.left G.right G.distinct s even
  weight := fun e => match e with
    | .inl e => G.weight e.val
    | .inr (.inl _) => (G.pathScale s N)^2
    | .inr (.inr (i,a)) => QuantumPathCode.coefficients
        (even i,G.pathScale s N,G.weight (qmaSelectedIndex s i)) ⟨a.val+1,by omega⟩
  constant := (G.constant+∑ i : Fin s.card, (3/4+3*(G.weight (qmaSelectedIndex s i))^2))+
    3*(s.card:ℚ)*(G.pathScale s N)^2

theorem subdivide_matrix (G : QMARationalExchangeGraph) (s : Finset G.Edge)
    (even : Fin s.card → Bool) (N : ℚ) :
    qmaExchangeMatrix (G.subdivide s even N).left (G.subdivide s even N).right
        (fun e => ((G.subdivide s even N).weight e:ℝ)) (G.subdivide s even N).constant =
      qmaPartialPaths G.left G.right (fun e => (G.weight e:ℝ)) G.constant N s even := by
  dsimp only [subdivide,qmaPartialPaths,qmaPathsGraph]
  congr 1
  · funext e
    rcases e with e | e
    · rfl
    rcases e with i | ⟨i,a⟩
    · simp [qmaParallelGraphWeight,pathScale_cast]
    · simpa only [qmaParallelGraphWeight,pathScale_cast] using
        QuantumPathCode.coefficients_spoke (even i,G.pathScale s N,G.weight (qmaSelectedIndex s i)) a
  · simp [qmaPathOffset,pathScale_cast]

theorem subdivide_energy_error (G : QMARationalExchangeGraph) (s : Finset G.Edge)
    (even : Fin s.card → Bool) {N : ℚ} (hN : 0 < N) :
    |(G.subdivide s even N).energy-G.energy| ≤ 1/(N:ℝ) := by
  unfold energy
  rw [G.subdivide_matrix]
  exact qmaPartialPaths_accuracy G.left G.right G.distinct (fun e => (G.weight e:ℝ))
    G.constant s even (by exact_mod_cast hN)

theorem subdivide_edge_count (G : QMARationalExchangeGraph) (s : Finset G.Edge)
    (even : Fin s.card → Bool) (N : ℚ) :
    Fintype.card (G.subdivide s even N).Edge = Fintype.card G.Edge+2*s.card :=
  qmaPartialPaths_edge_count s

end QMARationalExchangeGraph
end ContinuumCoulomb

end

end OAI
