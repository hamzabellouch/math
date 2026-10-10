import OAI.LinearAlgebra.MatrixMultiplication.FieldHistory.GroupMasks

namespace OAI

/-! Finite extraction histories, inherited masks and recovery bounds. -/

noncomputable section

namespace MatrixMultiplication.AllFieldHistoryGroupedRecovery

open AllFieldHistory AllFieldHistorySupport AllFieldHistoryChildLaws
open AllFieldHistoryGroupMasks JointPopulation JointCanonicalization JointCanonicalCW
open PermutationMatching
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

variable {K tick : ℕ}

abbrev GroupTarget (allocation : Allocation) (m : ℕ) (sigma : Placement) :=
  Target (groupCounts (K := K) (tick := tick) allocation m sigma)

def projectTarget (allocation : Allocation) (m : ℕ) (sigma : Placement)
    (e : AllFieldHistoryRecovery.Targets (K := K) (tick := tick) allocation m) :
    GroupTarget (K := K) (tick := tick) allocation m sigma := fun h => e h.val

def groupCoordinates (allocation : Allocation) (m : ℕ) (sigma : Placement)
    (e : GroupTarget (K := K) (tick := tick) allocation m sigma) :=
  pairEquiv (groupCounts allocation m sigma)
    (fun h => Fin (activeHalfLength h.val) → Fin 7)
    (fun h => Fin (activeHalfLength h.val) → Fin 7) e

def groupCoarse {sigma : Placement} (side : Fin 3) (h : ActiveOrder K tick sigma)
    (w : (Fin (activeHalfLength h.val) → Fin 7) × (Fin (activeHalfLength h.val) → Fin 7)) :=
  coarse activeHalfLength activeHalfLength AllFieldHistoryRecovery.halfLength_le_eight
    side h.val w

def groupIdealSide (allocation : Allocation) (m : ℕ) (ε : ℝ) (side : Fin 3)
    (sigma : Placement) (e : GroupTarget (K := K) (tick := tick) allocation m sigma)
    (w : GroupRaw (K := K) (tick := tick) allocation m sigma) : Prop :=
  coarseMask (groupCounts allocation m sigma)
      (fun h => Fin (activeHalfLength h.val) → Fin 7)
      (fun h => Fin (activeHalfLength h.val) → Fin 7) groupCoarse side e w ∧
    rawWindows (SL := fun h : ActiveOrder K tick sigma => Statistic h.val)
      (SR := fun h : ActiveOrder K tick sigma => Statistic h.val)
      (groupCounts allocation m sigma)
      (fun h => Fin (activeHalfLength h.val) → Fin 7)
      (fun h => Fin (activeHalfLength h.val) → Fin 7)
      (fun c => statistic c.1.val) (fun c => statistic c.1.val)
      (fun c => leftLaw c.1.val c.2 side) (fun c => rightLaw c.1.val c.2 side)
      (fun c => AllFieldHistoryMasks.childWidth ε c.1.val)
      (fun c => AllFieldHistoryMasks.childWidth ε c.1.val) e w

end MatrixMultiplication.AllFieldHistoryGroupedRecovery

end

end OAI
