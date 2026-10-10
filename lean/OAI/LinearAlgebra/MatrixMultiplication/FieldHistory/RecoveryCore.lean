import OAI.LinearAlgebra.MatrixMultiplication.FieldHistory.MaskCore
import OAI.LinearAlgebra.MatrixMultiplication.FieldHistory.RawMasks
import OAI.LinearAlgebra.MatrixMultiplication.FieldHistory.IncomingCore
import OAI.LinearAlgebra.MatrixMultiplication.JointExtraction.CanonicalMixed
import OAI.LinearAlgebra.MatrixMultiplication.Recovery.EquivOrbitTransport

namespace OAI

/-! Finite extraction histories, inherited masks and recovery bounds. -/

noncomputable section

namespace MatrixMultiplication.AllFieldHistoryRecovery

open MatrixMultiplication.Foundation AllFieldHistory AllFieldHistoryChildLaws
open AllFieldHistorySupport JointPopulation JointCanonicalization JointCanonicalCW
open PermutationMatching
open scoped BigOperators

attribute [local instance] Classical.propDecidable Classical.decEq

variable {K tick : ℕ}

theorem halfLength_le_eight (h : Active K tick) : activeHalfLength h ≤ 8 := by
  rcases h with ⟨⟨w, phi⟩, hh⟩
  cases w <;> norm_num [activeHalfLength, Work.halfLength]

abbrev Raw (allocation : Allocation) (m : ℕ) :=
  ActiveRawPairs (K := K) (tick := tick) allocation m

abbrev Targets (allocation : Allocation) (m : ℕ) :=
  Target (activeCounts (K := K) (tick := tick) allocation m)

abbrev Symmetries (allocation : Allocation) (m : ℕ) :=
  HalfClassPermutations (ClassPositions
    (activeCounts (K := K) (tick := tick) allocation m))

def childStatistic (_side : Fin 3) (c : Active K tick × JointPopulation.Shape) :=
  statistic c.1

def leftPrescription (side : Fin 3) (c : Active K tick × JointPopulation.Shape) :=
  leftLaw c.1 c.2 side

def rightPrescription (side : Fin 3) (c : Active K tick × JointPopulation.Shape) :=
  rightLaw c.1 c.2 side

def outputWidth (ε : ℝ) (_side : Fin 3) (c : Active K tick × JointPopulation.Shape) :=
  AllFieldHistoryMasks.childWidth ε c.1

def parents (F : Type*) [CommRing F] (h : Active K tick) :=
  JointCanonicalMixed.inputTensor (F := F) activeHalfLength activeHalfLength
    activeParentShape (fun _ => true) h

def rawSource (F : Type*) [CommRing F] (allocation : Allocation) (m : ℕ) :
    Tensor F (Raw (K := K) (tick := tick) allocation m)
      (Raw (K := K) (tick := tick) allocation m) (Raw (K := K) (tick := tick) allocation m) :=
  sourceTensor (activeCounts allocation m) (Left activeHalfLength)
    (Right activeHalfLength) (parents F)

def ideal (F : Type*) [CommRing F] (allocation : Allocation) (m : ℕ) (ε : ℝ)
    (e : Targets (K := K) (tick := tick) allocation m) :
    Tensor F (Raw (K := K) (tick := tick) allocation m) (Raw (K := K) (tick := tick) allocation m) (Raw (K := K) (tick := tick) allocation m) :=
  JointCanonicalization.ideal (activeCounts allocation m)
    (Left activeHalfLength) (Right activeHalfLength) (parents F)
    (coarse activeHalfLength activeHalfLength halfLength_le_eight)
    childStatistic childStatistic leftPrescription rightPrescription
    (outputWidth ε) (outputWidth ε) e

def coordinates (allocation : Allocation) (m : ℕ)
    (e : Targets (K := K) (tick := tick) allocation m) :=
  pairEquiv (activeCounts allocation m) (Left activeHalfLength)
    (Right activeHalfLength) e

def canonical (F : Type*) [CommRing F] (allocation : Allocation) (m : ℕ) (ε : ℝ) :
    Tensor F (AllFieldHistoryMasks.Words (K := K) (tick := tick) allocation m)
      (AllFieldHistoryMasks.Words (K := K) (tick := tick) allocation m) (AllFieldHistoryMasks.Words (K := K) (tick := tick) allocation m) :=
  canonicalIdeal (activeCounts allocation m) (Left activeHalfLength)
    (Right activeHalfLength) (parents F)
    (coarse activeHalfLength activeHalfLength halfLength_le_eight)
    childStatistic childStatistic leftPrescription rightPrescription
    (outputWidth ε) (outputWidth ε)

@[instance_reducible]
def rawAction (allocation : Allocation) (m : ℕ)
    (e : Targets (K := K) (tick := tick) allocation m) :
    MulAction (Symmetries (K := K) (tick := tick) allocation m) (Raw (K := K) (tick := tick) allocation m) :=
  EquivOrbitTransport.action (coordinates allocation m e)

def completeKeep (allocation : Allocation) (m : ℕ) (ε : ℝ) (side : Fin 3)
    (w : Raw (K := K) (tick := tick) allocation m) : Prop :=
  JointCanonicalMixed.sideMask (activeCounts allocation m)
      activeHalfLength activeHalfLength halfLength_le_eight side w ∧
    AllFieldHistoryIncomingMasks.received allocation m ε side w ∧
    AllFieldHistoryRawMasks.rawPass allocation m ε side w

def sideVariable {V : Type*} (side : Fin 3) (x y z : V) : V := ![x, y, z] side

def idealSide (allocation : Allocation) (m : ℕ) (ε : ℝ) (side : Fin 3)
    (e : Targets (K := K) (tick := tick) allocation m) (w : Raw (K := K) (tick := tick) allocation m) : Prop :=
  coarseMask (activeCounts allocation m) (Left activeHalfLength) (Right activeHalfLength)
      (coarse activeHalfLength activeHalfLength halfLength_le_eight) side e w ∧
    rawWindows (activeCounts allocation m) (Left activeHalfLength) (Right activeHalfLength)
      (childStatistic side) (childStatistic side) (leftPrescription side)
      (rightPrescription side) (outputWidth ε side) (outputWidth ε side) e w

end MatrixMultiplication.AllFieldHistoryRecovery

end

end OAI
