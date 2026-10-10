import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumForkListCalibration

namespace OAI

/-! The complete literal round is the retained matrix plus the calibrated
five-bond packets, including the newly active center-to-mediator edges. -/

noncomputable section
namespace ContinuumCoulomb.QuantumForkList
open MediatorListProgram QuantumRawExchange

def freshBonds (s : State) (R : ℚ) : List Bond :=
  (List.range (pairCount s.2.2.2)).map (fun e =>
    ((((catalog s.2.2.2).drop e).headD (0,((0,0),(0,0)))).1,s.1+2*e,R))

def packets (s : State) (R : ℚ) : List Bond :=
  ((List.range (pairCount s.2.2.2)).map (fun e =>
    pairBonds s.1 e R (((catalog s.2.2.2).drop e).headD (0,((0,0),(0,0)))).2 ++
      [((((catalog s.2.2.2).drop e).headD (0,((0,0),(0,0)))).1,s.1+2*e,R)])).flatten

theorem packets_sum {M : Type*} [AddCommMonoid M] (s : State) (R : ℚ) (f : Bond → M) :
    ((packets s R).map f).sum =
      ((addedBonds s R).map f).sum+((freshBonds s R).map f).sum := by
  simp only [packets,addedBonds,freshBonds,List.map_flatten,List.sum_flatten,List.map_map,
    Function.comp_def,List.map_append,List.sum_append,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,catalog_length,List.sum_map_add]

theorem next_matrix_packets (N : ℚ) (s : State) :
    matrix (next N s) =
      rawMatrix (s.1+2*pairCount s.2.2.2)
        (background s++packets s (scale N s),(next N s).2.2.1) := by
  dsimp only [matrix,next]
  simp only [rawMatrix,List.map_append,List.sum_append,
    next_active_sum,background,packets_sum,freshBonds,List.map_map,Function.comp_def]
  abel

end ContinuumCoulomb.QuantumForkList

end

end OAI
