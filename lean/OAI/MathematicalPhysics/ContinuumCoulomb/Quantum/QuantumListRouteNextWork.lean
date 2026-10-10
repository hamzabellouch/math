import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumListRouteNextPoint

namespace OAI

/-! Exact remaining-work values in the finite output edge order. -/

noncomputable section
namespace ContinuumCoulomb.QuantumListRouteProgram
open QuantumListSchedule QuantumRouteCode
open scoped Classical

private theorem work_map (N : ℚ) (s : QuantumListSchedule.State) (hs : Valid s)
    (e : Fin (QuantumListSchedule.value (N,s)).2.2.length) :
    (schedule (QuantumListSchedule.value (N,s)) (value_valid (N,s) hs)).work e =
      ((schedule s hs).next N).work (nextEdge (N,s) hs e) :=
  (nextRelabel (N,s) hs).work e

theorem next_work_retained (N : ℚ) (s : QuantumListSchedule.State) (hs : Valid s)
    (i : Fin (partition false s.2.2).length) :
    (schedule (QuantumListSchedule.value (N,s)) (value_valid (N,s) hs)).work
      ((tagEquiv (N,s)).symm (.inl i))=0 := by
  exact (work_map N s hs _).trans
    (congrArg ((schedule s hs).next N).work (next_edge_retained N s hs i))

theorem next_work_central (N : ℚ) (s : QuantumListSchedule.State) (hs : Valid s)
    (i : Fin (partition true s.2.2).length) :
    (schedule (QuantumListSchedule.value (N,s)) (value_valid (N,s) hs)).work
      ((tagEquiv (N,s)).symm (.inr (i,0)))=0 := by
  exact (work_map N s hs _).trans
    (congrArg ((schedule s hs).next N).work (next_edge_central N s hs i))

theorem next_work_left (N : ℚ) (s : QuantumListSchedule.State) (hs : Valid s)
    (i : Fin (partition true s.2.2).length) :
    (schedule (QuantumListSchedule.value (N,s)) (value_valid (N,s) hs)).work
      ((tagEquiv (N,s)).symm (.inr (i,1)))=0 := by
  exact (work_map N s hs _).trans
    (congrArg ((schedule s hs).next N).work (next_edge_left N s hs i))

theorem next_work_right (N : ℚ) (s : QuantumListSchedule.State) (hs : Valid s)
    (i : Fin (partition true s.2.2).length) :
    (schedule (QuantumListSchedule.value (N,s)) (value_valid (N,s) hs)).work
      ((tagEquiv (N,s)).symm (.inr (i,2))) =
      (schedule s hs).work (qmaSelectedIndex (schedule s hs).active (activePermutation s hs i))-1 := by
  exact (work_map N s hs _).trans
    (congrArg ((schedule s hs).next N).work (next_edge_right N s hs i))

end ContinuumCoulomb.QuantumListRouteProgram

end

end OAI
