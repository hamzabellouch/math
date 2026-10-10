import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumHistoryParameterBounds
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumRawOutputSize
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumHistoryLattice

namespace OAI

/-! Linear size and box bounds for the exact spatial graph before routing. -/

noncomputable section
namespace ContinuumCoulomb.QuantumHistorySpatial
open QuantumOrderedSourceIndex QuantumPaddedLabelProgram QuantumForkList

def rawBondFactor : ℕ := 6*(1+3717*8192)+22*(12544*8192)
def spatialSizeFactor (D : ℕ) : ℕ := 4*(1+3717*8192)+(5+12*D)*rawBondFactor

theorem history_bonds_linear (c : QMACircuit) (hT : 0 < c.gates.length) (N : ℕ) :
    (historyOutput c hT N).1.length ≤ rawBondFactor*qubitCount c := by
  have h := historyOutput_length c hT N
  have hm := termCount_bound c
  calc
    _ ≤ 6*(qubitCount c+3717*termCount c)+22*(12544*termCount c) := h
    _ ≤ 6*(qubitCount c+3717*(8192*qubitCount c))+
        22*(12544*(8192*qubitCount c)) := by gcongr
    _ = _ := by unfold rawBondFactor; ring

theorem model_size_linear (c : QMACircuit) (hc : c.WellFormed)
    (hT : 0 < (qmaSparseCircuit c).gates.length)
    (hne : (qmaNearestCircuit c).gates ≠ []) (N : ℕ) :
    (model c hc hT hne N).n+Fintype.card (model c hc hT hne N).Term ≤
      spatialSizeFactor historyDegree*qubitCount (qmaSparseCircuit c) := by
  have h := (input c hc hT hne N).model_size
  rw [input_n,historyQubits_eq,input_bonds] at h
  have hb := history_bonds_linear (qmaSparseCircuit c) hT N
  have hm := termCount_bound (qmaSparseCircuit c)
  calc
    _ ≤ 4*(qubitCount (qmaSparseCircuit c)+3717*termCount (qmaSparseCircuit c))+
        5*(historyOutput (qmaSparseCircuit c) hT N).1.length+
        12*historyDegree*(historyOutput (qmaSparseCircuit c) hT N).1.length := h
    _ ≤ 4*(qubitCount (qmaSparseCircuit c)+3717*(8192*qubitCount (qmaSparseCircuit c)))+
        5*(rawBondFactor*qubitCount (qmaSparseCircuit c))+
        12*historyDegree*(rawBondFactor*qubitCount (qmaSparseCircuit c)) := by gcongr
    _ = _ := by unfold spatialSizeFactor; ring

theorem model_rows_bound (c : QMACircuit) (hc : c.WellFormed)
    (hT : 0 < (qmaSparseCircuit c).gates.length)
    (hne : (qmaNearestCircuit c).gates ≠ []) (N : ℕ) :
    (model c hc hT hne N).rows ≤ qubitCount (qmaSparseCircuit c) := by
  rw [model,SpatialInput.model_rows,qubitCount_eq]
  change (qmaNearestCircuit c).gates.length ≤
    3*(qmaSparseCircuit c).gates.length+
      2*(c.work+(qmaNearestCircuit c).gates.length*(c.work+1))+8
  nlinarith

theorem model_width_bound (c : QMACircuit) (hc : c.WellFormed)
    (hT : 0 < (qmaSparseCircuit c).gates.length)
    (hne : (qmaNearestCircuit c).gates ≠ []) (N : ℕ) :
    (model c hc hT hne N).width ≤ qubitCount (qmaSparseCircuit c) := by
  rw [model,SpatialInput.model_width,qubitCount_eq]
  change c.work ≤ 3*(qmaSparseCircuit c).gates.length+
    2*(c.work+(qmaNearestCircuit c).gates.length*(c.work+1))+8
  omega

def boxFactor (A B : ℕ) : ℕ := 256*(8*(9*B+9))*(A+1)

theorem model_box_bound {A B n : ℕ} (M : QMASpatialExchangeModel A B)
    (hr : M.rows ≤ n) (hw : M.width ≤ n) :
    256*M.bufferedWidth ≤ boxFactor A B*(n+1) ∧
    256*M.bufferedHeight ≤ boxFactor A B*(n+1) := by
  constructor
  · calc
      _ = 256*(8*(9*B+9))*A*(M.rows+1) := by unfold QMASpatialExchangeModel.bufferedWidth; ring
      _ ≤ 256*(8*(9*B+9))*(A+1)*(n+1) := by gcongr; omega
      _ = _ := rfl
  · calc
      _ = 256*(8*(9*B+9))*1*(M.width+1) := by unfold QMASpatialExchangeModel.bufferedHeight; ring
      _ ≤ 256*(8*(9*B+9))*(A+1)*(n+1) := by gcongr; omega
      _ = _ := rfl

end ContinuumCoulomb.QuantumHistorySpatial

end

end OAI
