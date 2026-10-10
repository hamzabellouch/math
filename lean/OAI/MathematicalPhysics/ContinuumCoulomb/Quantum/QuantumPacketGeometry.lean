import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumListGraph
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumListPathStep

namespace OAI

/-! A finite bond packet represents a placed graph when its exact position
array and unordered edge support agree under a vertex permutation. -/

noncomputable section
namespace ContinuumCoulomb

structure QMAPacketGeometry (G : QMARationalExchangeGraph)
    (position : Fin G.n → ℕ × ℕ) (q : QuantumListPathStep.Output)
    (ps : List (ℕ × ℕ)) : Prop where
  bounded : SourceBondLists.bounded q.1 q.2.1
  noLoops : ∀ b ∈ q.2.1, b.1 ≠ b.2.1
  matching :
    let H := QuantumListGraph.ofBonds q.1 q.2.1 q.2.2 bounded noLoops
    ∃ vertex : Fin H.n ≃ Fin G.n,
      ps = List.ofFn (fun v => position (vertex v)) ∧
      (∀ e : H.Edge, ∃ f : G.Edge,
        s(vertex (H.left e),vertex (H.right e)) = s(G.left f,G.right f)) ∧
      (∀ f : G.Edge, ∃ e : H.Edge,
        s(vertex (H.left e),vertex (H.right e)) = s(G.left f,G.right f))

end ContinuumCoulomb

end

end OAI
