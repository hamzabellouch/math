import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumGateCode
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumSweepCircuit

namespace OAI

/-! Natural-number formulas for the checked row sweep. These formulas keep
the same operand order and insertion point as the physical circuit. -/

noncomputable section
namespace ContinuumCoulomb.QuantumCircuitCode

def sweepIndex (width row k : ℕ) : ℕ := if row%2=0 then k else width-k

theorem sweepIndex_value (width row : ℕ) (i : Fin (width+1)) :
    (qmaSweepOrder width row i).val=sweepIndex width row i.val := by
  by_cases h : row%2=0
  · simp only [qmaSweepOrder,sweepIndex,h,ite_true,Equiv.refl_apply]
  · simp [qmaSweepOrder,sweepIndex,h,Fin.revPerm,Fin.rev]

theorem sweepIndex_inverse (width row : ℕ) (i : Fin (width+1)) :
    ((qmaSweepOrder width row).symm i).val=sweepIndex width row i.val := by
  by_cases h : row%2=0
  · simp only [qmaSweepOrder,sweepIndex,h,ite_true,Equiv.refl_symm,Equiv.refl_apply]
  · simp [qmaSweepOrder,sweepIndex,h,Fin.revPerm,Fin.rev]

def rowCut (width row : ℕ) (g : QMAGate) : ℕ :=
  let i := sweepIndex width row (gateLeft g%(width+1))
  let j := sweepIndex width row (gateRight g%(width+1))
  if gateTag g=2 then max i j+1 else i+1

theorem rowCut_eq (width row : ℕ) (g : QMAGate) :
    qmaGateCut width (qmaSweepOrder width row) g=rowCut width row g := by
  cases g <;> simp [qmaGateCut,qmaGateSites,rowCut,gateTag,gateLeft,gateRight,
    sweepIndex_inverse,qmaQubit]

def rowAddress (width row i : ℕ) : ℕ := row*(width+1)+i%(width+1)

def mapToRow (width row : ℕ) : QMAGate → QMAGate
  | .hadamard i => .hadamard (rowAddress width row i)
  | .phaseT i => .phaseT (rowAddress width row i)
  | .controlledNot i j => .controlledNot (rowAddress width row i) (rowAddress width row j)

theorem mapToRow_eq (rows width : ℕ) (row : Fin (rows+1)) (g : QMAGate) :
    qmaMapGate width (qmaGridWork rows width) (qmaGridQubit rows width row) g=
      mapToRow width row.val g := by
  cases g <;> rfl

def rowPairs (width row order : ℕ) : List (ℕ × ℕ) :=
  (List.range (width+1)).map (fun k =>
    (row*(width+1)+sweepIndex width order k,
      (row+1)*(width+1)+sweepIndex width order k))

theorem rowPairs_eq (rows width : ℕ) (row : Fin rows) (order : ℕ) :
    (qmaRowPairs (qmaGridQubit rows width row.castSucc ∘ qmaSweepOrder width order)
      (qmaGridQubit rows width row.succ ∘ qmaSweepOrder width order)).map
        (fun p => (p.1.val,p.2.val))=rowPairs width row.val order := by
  apply List.ext_getElem
  · simp only [qmaRowPairs,rowPairs,List.length_map,List.length_ofFn,List.length_range]
  · intro i hi hj
    simp only [qmaRowPairs,rowPairs,List.getElem_map,List.getElem_ofFn,List.getElem_range,
      Function.comp_apply,qmaGridQubit,Fin.val_castSucc,Fin.val_succ,sweepIndex_value]

def transferList (ps : List (ℕ × ℕ)) : List QMAGate :=
  ps.flatMap (fun p => [.controlledNot p.1 p.2,.controlledNot p.2 p.1,.controlledNot p.1 p.2])

theorem transferList_eq {work : ℕ} (ps : List (Fin (work+1) × Fin (work+1))) :
    qmaTransferGates ps=transferList (ps.map (fun p => (p.1.val,p.2.val))) := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    simp only [qmaTransferGates,List.map_cons,transferList,List.flatMap_cons,qmaWireSwapGates]
    rw [ih]
    rfl

def rowStage (rows width start : ℕ) (g : QMAGate) : List QMAGate :=
  let order := rows-1-start
  let ps := rowPairs width start order
  let cut := rowCut width order g
  transferList (ps.take cut)++[mapToRow width (start+1) g]++transferList (ps.drop cut)

theorem rowStage_eq (rows width start : ℕ) (h : start < rows) (g : QMAGate) :
    qmaRowStage width (qmaGridWork rows width)
      (qmaGridQubit rows width ⟨start,by omega⟩)
      (qmaGridQubit rows width ⟨start+1,by omega⟩)
      (qmaSweepOrder width (rows-1-start)) g=rowStage rows width start g := by
  unfold qmaRowStage rowStage
  dsimp only
  rw [rowCut_eq,transferList_eq,transferList_eq,List.map_take,List.map_drop]
  have hp := rowPairs_eq rows width ⟨start,h⟩ (rows-1-start)
  simp only [Fin.castSucc_mk,Fin.succ_mk] at hp
  rw [hp,mapToRow_eq]

end ContinuumCoulomb.QuantumCircuitCode

end

end OAI
