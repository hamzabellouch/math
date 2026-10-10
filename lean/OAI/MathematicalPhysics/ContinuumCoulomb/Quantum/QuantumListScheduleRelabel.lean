import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumPathRelabelingIteration
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumListScheduleRealization

namespace OAI

/-! The emitted schedule has exactly the canonical subdivided coordinates,
up to its explicit finite vertex and edge permutations. -/

noncomputable section
namespace ContinuumCoulomb.QuantumListSchedule
open scoped Classical

def iterateRelabel (N : ℚ) (s : State) (hs : Valid s) : (k : ℕ) →
    QMAPathRelabeling (schedule (iterate N k s) (iterate_valid N s hs k))
      ((schedule s hs).iterate N k)
  | 0 => QMAPathRelabeling.refl _
  | k+1 => (nextRelabel (N,iterate N k s) (iterate_valid N s hs k)).trans
      ((iterateRelabel N s hs k).next N)

theorem iterateRelabel_geometry {Γ : SimpleGraph (ℕ × ℕ)}
    (N : ℚ) (s : State) (hs : Valid s) (P : QMAPathEmbedding (schedule s hs) Γ) (k : ℕ) :
    (∀ v, (P.iterate N k).position ((iterateRelabel N s hs k).vertex v)=
      (iterateEmbedding N s hs P k).position v) ∧
    (∀ e j, (P.iterate N k).point ((iterateRelabel N s hs k).edge e) j=
      (iterateEmbedding N s hs P k).point e j) := by
  induction k with
  | zero => exact ⟨fun _ => rfl,fun _ _ => rfl⟩
  | succ k ih =>
    let E := iterateRelabel N s hs k
    let F := nextRelabel (N,iterate N k s) (iterate_valid N s hs k)
    constructor
    · intro v
      exact (E.next_position (iterateEmbedding N s hs P k) (P.iterate N k)
        ih.1 ih.2 N (F.vertex v)).trans (by rfl)
    · intro e j
      exact (E.next_point (iterateEmbedding N s hs P k) (P.iterate N k)
        ih.2 N (F.edge e) j).trans (by rfl)

end ContinuumCoulomb.QuantumListSchedule

end

end OAI
