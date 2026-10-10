import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumListRouteNextPosition

namespace OAI

/-! Exact route-index formulas for the three emitted edges of a selected
source edge and for every retained edge. -/

noncomputable section
namespace ContinuumCoulomb.QuantumListRouteProgram
open QuantumListSchedule QuantumRouteCode
open scoped Classical

variable {Γ : SimpleGraph Pair}

theorem next_edge_retained (N : ℚ) (s : QuantumListSchedule.State) (hs : Valid s)
    (i : Fin (partition false s.2.2).length) :
    nextEdge (N,s) hs ((tagEquiv (N,s)).symm (.inl i)) = .inl (retainedEquiv s hs i) := by
  exact nextEdge_tag (N,s) hs (.inl i)

theorem next_edge_central (N : ℚ) (s : QuantumListSchedule.State) (hs : Valid s)
    (i : Fin (partition true s.2.2).length) :
    nextEdge (N,s) hs ((tagEquiv (N,s)).symm (.inr (i,0))) =
      .inr (.inl (activePermutation s hs i)) := by
  exact nextEdge_tag (N,s) hs (.inr (i,0))

theorem next_edge_left (N : ℚ) (s : QuantumListSchedule.State) (hs : Valid s)
    (i : Fin (partition true s.2.2).length) :
    nextEdge (N,s) hs ((tagEquiv (N,s)).symm (.inr (i,1))) =
      .inr (.inr (activePermutation s hs i,0)) := by
  exact nextEdge_tag (N,s) hs (.inr (i,1))

theorem next_edge_right (N : ℚ) (s : QuantumListSchedule.State) (hs : Valid s)
    (i : Fin (partition true s.2.2).length) :
    nextEdge (N,s) hs ((tagEquiv (N,s)).symm (.inr (i,2))) =
      .inr (.inr (activePermutation s hs i,1)) := by
  exact nextEdge_tag (N,s) hs (.inr (i,2))

theorem next_point (N : ℚ) (s : QuantumListSchedule.State) (hs : Valid s)
    (P : QMAPathEmbedding (schedule s hs) Γ) (e : Fin (QuantumListSchedule.value (N,s)).2.2.length)
    (k : ℕ) : (nextEmbedding (N,s) hs P).point e k =
      (P.next N).point (nextEdge (N,s) hs e) k := rfl

theorem next_point_retained (N : ℚ) (s : QuantumListSchedule.State) (hs : Valid s)
    (P : QMAPathEmbedding (schedule s hs) Γ) (i : Fin (partition false s.2.2).length) (k : ℕ) :
    (nextEmbedding (N,s) hs P).point ((tagEquiv (N,s)).symm (.inl i)) k =
      P.point (retainedEquiv s hs i).val k := by
  rw [next_point,next_edge_retained]
  rfl

theorem next_point_central (N : ℚ) (s : QuantumListSchedule.State) (hs : Valid s)
    (P : QMAPathEmbedding (schedule s hs) Γ) (i : Fin (partition true s.2.2).length) (k : ℕ) :
    (nextEmbedding (N,s) hs P).point ((tagEquiv (N,s)).symm (.inr (i,0))) k =
      P.point (qmaSelectedIndex (schedule s hs).active (activePermutation s hs i)) (k+1) := by
  rw [next_point,next_edge_central]
  rfl

theorem next_point_left (N : ℚ) (s : QuantumListSchedule.State) (hs : Valid s)
    (P : QMAPathEmbedding (schedule s hs) Γ) (i : Fin (partition true s.2.2).length) (k : ℕ) :
    (nextEmbedding (N,s) hs P).point ((tagEquiv (N,s)).symm (.inr (i,1))) k =
      P.point (qmaSelectedIndex (schedule s hs).active (activePermutation s hs i)) k := by
  rw [next_point,next_edge_left]
  rfl

theorem next_point_right (N : ℚ) (s : QuantumListSchedule.State) (hs : Valid s)
    (P : QMAPathEmbedding (schedule s hs) Γ) (i : Fin (partition true s.2.2).length) (k : ℕ) :
    (nextEmbedding (N,s) hs P).point ((tagEquiv (N,s)).symm (.inr (i,2))) k =
      P.point (qmaSelectedIndex (schedule s hs).active (activePermutation s hs i))
        (2*(schedule s hs).work
          (qmaSelectedIndex (schedule s hs).active (activePermutation s hs i))+1-k) := by
  rw [next_point,next_edge_right]
  rfl

end ContinuumCoulomb.QuantumListRouteProgram

end

end OAI
