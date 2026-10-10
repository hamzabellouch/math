import OAI.LinearAlgebra.MatrixMultiplication.FieldHistory.MaskCore
import OAI.LinearAlgebra.MatrixMultiplication.FieldHistory.Tensors

namespace OAI

/-! Finite extraction histories, inherited masks and recovery bounds. -/

noncomputable section

namespace MatrixMultiplication.AllFieldHistoryIncomingMasks

open MatrixMultiplication.Foundation AllFieldHistory AllFieldParameters
open AllFieldHistoryChildLaws AllFieldHistorySupport AllFieldHistoryMasks
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

variable {K tick : ℕ}

def joinHalves (w : Work K) :
    ((Fin w.halfLength → Fin 7) × (Fin w.halfLength → Fin 7)) →
      (Fin (currentLength w.source) → Fin 7) :=
  match w with
  | .stageA _ => fun x => Fin.append x.1 x.2
  | .stageB _ => fun x => Fin.append x.1 x.2
  | .stageC _ => fun x => Fin.append x.1 x.2

def sourcePositionsEquiv (allocation : Allocation) (m : ℕ) (h : Active K tick) :
    JointPopulation.Positions (activeCounts allocation m) h ≃
      Fin (population allocation m (h.val.1.source, h.val.2)) :=
  finCongr (jointCounts_sum allocation m h.val)

def incomingWord (allocation : Allocation) (m : ℕ) (h : Active K tick)
    (w : ActiveRawPairs (K := K) (tick := tick) allocation m) :
    HistoryWord allocation m (h.val.1.source, h.val.2) :=
  fun p => joinHalves h.val.1 (w h ((sourcePositionsEquiv allocation m h).symm p))

def received (allocation : Allocation) (m : ℕ) (ε : ℝ) (side : Fin 3)
    (w : ActiveRawPairs (K := K) (tick := tick) allocation m) : Prop :=
  ∀ h : Active K tick,
    residentMask allocation m ε (h.val.1.source, h.val.2) side
      (incomingWord allocation m h w)

end MatrixMultiplication.AllFieldHistoryIncomingMasks

end

end OAI
