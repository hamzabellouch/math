import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumSweepListProgram
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumSweepCongestion

namespace OAI

/-! Literal natural row/column tags for the sparse sweep.  The
three gates of each wire transfer carry the same column; the original gate
keeps its proved arrival column. -/

noncomputable section
namespace ContinuumCoulomb.QuantumSweepCells
open QuantumCircuitCode

def repeatColumns (xs : List ℕ) : List ℕ := xs.flatMap (fun j => [j,j,j])

def columns (width order : ℕ) : List ℕ :=
  (List.range (width+1)).map (sweepIndex width order)

def rowColumns (width order : ℕ) (g : QMAGate) : List ℕ :=
  let xs := columns width order
  let cut := rowCut width order g
  repeatColumns (xs.take cut) ++ [sweepIndex width order (cut-1)] ++
    repeatColumns (xs.drop cut)

def rowCells (rows width start : ℕ) (g : QMAGate) : List (ℕ × ℕ) :=
  (rowColumns width (rows-1-start) g).map (fun j => (start,j))

def sweepCells (rows width start : ℕ) (gs : List QMAGate) : List (ℕ × ℕ) :=
  (List.range gs.length).flatMap (fun i =>
    rowCells rows width (start+i) (readGate gs i))

def value (c : QMACircuit) : List (ℕ × ℕ) :=
  sweepCells (qmaNearestCircuit c).gates.length c.work 0 (qmaNearestCircuit c).gates

theorem transfer_columns {width work : ℕ}
    (l r : Fin (width+1) → Fin (work+1)) (xs : List (Fin (width+1))) :
    (qmaColumnTransfer l r xs).map (fun p => p.2.val)=
      repeatColumns (xs.map Fin.val) := by
  induction xs with
  | nil => rfl
  | cons j xs ih =>
    simp only [qmaColumnTransfer,List.flatMap_cons,List.map_append,
      qmaWireSwapGates,List.map_cons,List.map_nil,repeatColumns]
    simpa only [repeatColumns,qmaColumnTransfer,qmaWireSwapGates,List.map_cons,List.map_nil]
      using congrArg (fun ys => [j.val,j.val,j.val]++ys) ih

theorem columns_actual (width order : ℕ) :
    (List.ofFn (qmaSweepOrder width order)).map Fin.val=columns width order := by
  apply List.ext_getElem
  · simp only [List.length_map,List.length_ofFn,columns,List.length_range]
  · intro i hi hj
    simp only [List.getElem_map,List.getElem_ofFn,columns,List.getElem_range,
      sweepIndex_value]

theorem arrival_actual (width order : ℕ) (g : QMAGate) :
    (qmaGateArrivalColumn width (qmaSweepOrder width order) g).val=
      sweepIndex width order (rowCut width order g-1) := by
  rw [qmaGateArrivalColumn,sweepIndex_value]
  simp only [qmaGateArrivalIndex,rowCut_eq]

theorem rowColumns_actual (width work order : ℕ)
    (l r : Fin (width+1) → Fin (work+1)) (g : QMAGate) :
    (qmaTaggedRowStage width work l r (qmaSweepOrder width order) g).map
        (fun p => p.2.val)=rowColumns width order g := by
  simp only [qmaTaggedRowStage,List.map_append,List.map_cons,List.map_nil,
    transfer_columns,List.map_take,List.map_drop,columns_actual,rowCut_eq,
    arrival_actual,rowColumns]

theorem rowCells_actual (rows width start : ℕ) (hs : start < rows) (g : QMAGate) :
    ((qmaTaggedRowStage width (qmaGridWork rows width)
      (qmaGridQubit rows width ⟨start,by omega⟩)
      (qmaGridQubit rows width ⟨start+1,by omega⟩)
      (qmaSweepOrder width (rows-1-start)) g).map
        (fun p => (p.1,((⟨start,by omega⟩ : Fin (rows+1)),p.2)))).map
        (fun p => (p.2.1.val,p.2.2.val))=rowCells rows width start g := by
  simpa only [List.map_map,Function.comp_def,rowCells] using
    congrArg (List.map (fun j => (start,j)))
      (rowColumns_actual width (qmaGridWork rows width) (rows-1-start)
        (qmaGridQubit rows width ⟨start,by omega⟩)
        (qmaGridQubit rows width ⟨start+1,by omega⟩) g)

theorem sweepCells_cons (rows width start : ℕ) (g : QMAGate) (gs : List QMAGate) :
    sweepCells rows width start (g::gs)=
      rowCells rows width start g++sweepCells rows width (start+1) gs := by
  simp only [sweepCells,List.length_cons,List.range_succ_eq_map,List.flatMap_cons,
    List.flatMap_map,readGate,List.drop_zero,List.headD_cons,Nat.add_zero,List.drop_succ_cons]
  congr 1
  have h : (fun i => rowCells rows width (start+Nat.succ i)
      ((gs.drop i).headD (.hadamard 0)))=
      (fun i => rowCells rows width (start+1+i) ((gs.drop i).headD (.hadamard 0))) := by
    funext i
    congr 1
    omega
  rw [h]

theorem sweepCells_actual (rows width start : ℕ) (gs : List QMAGate)
    (h : start+gs.length ≤ rows) :
    (qmaTaggedSweepFrom rows width start gs h).map
      (fun p => (p.2.1.val,p.2.2.val))=sweepCells rows width start gs := by
  induction gs generalizing start with
  | nil => rfl
  | cons g gs ih =>
    have hs : start < rows := by simp only [List.length_cons] at h; omega
    rw [sweepCells_cons]
    simp only [qmaTaggedSweepFrom,List.map_append]
    rw [rowCells_actual rows width start hs g,ih]

theorem value_actual (c : QMACircuit) :
    value c=(qmaSparseTags c).map (fun p => (p.2.1.val,p.2.2.val)) :=
  (sweepCells_actual _ _ _ _ _).symm

theorem value_length (c : QMACircuit) :
    (value c).length=(qmaSparseCircuit c).gates.length := by
  rw [value_actual,List.length_map,qmaSparseTags_length]

end ContinuumCoulomb.QuantumSweepCells

end

end OAI
