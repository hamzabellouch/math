import OAI.MathematicalPhysics.ContinuumCoulomb.Programs.SourcePrograms
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumCircuitPadding
import OAI.Computability.QuantumFactoring.BitStackSumInjection

namespace OAI

/-! Actual parsing of the verifier's prefix circuit encoding. Register sizes
are clipped to supplied unary bounds before later finite enumerations. -/

noncomputable section
namespace ContinuumCoulomb.QuantumCircuitCode
open ExactQuantumFactoring.BitStackProgram
open PrefixPrograms

def gateCode (g : QMAGate) : List Bool :=
  sumCode (sumCode Nat.bits Nat.bits) (prodCode Nat.bits Nat.bits) (qmaGateEquiv g)

def rawCode (c : QMACircuit) : List Bool :=
  prodCode Nat.bits (prodCode Nat.bits (listCode gateCode)) (qmaCircuitEquiv c)

def circuitCode (c : QMACircuit) : List Bool :=
  prodCode unaryCode (prodCode unaryCode (listCode gateCode)) (qmaCircuitEquiv c)

private def sumView {α β : Type} (x : (α ⊕ β) × List Bool) :
    (α × List Bool) ⊕ (β × List Bool) :=
  match x.1 with
  | .inl a => .inl (a,x.2)
  | .inr b => .inr (b,x.2)

private noncomputable def sumSplitter {α β : Type}
    (c : BinaryEncoding.Codec α) (d : BinaryEncoding.Codec β)
    (pc : Splitter c) (pd : Splitter d) : Splitter (BinaryEncoding.sum c d) := by
  let outCode := prodCode (BinaryEncoding.sum c d).encode id
  let left : Procedure (prefixCode c) outCode
      (fun x : α × List Bool => (Sum.inl x.1,x.2)) :=
    (((Procedure.sumLeft c.encode d.encode).comp
      ((Procedure.first c.encode id).comp pc)).pair
        ((Procedure.second c.encode id).comp pc)).result (by intro x; rfl)
  let right : Procedure (prefixCode d) outCode
      (fun x : β × List Bool => (Sum.inr x.1,x.2)) :=
    (((Procedure.sumRight c.encode d.encode).comp
      ((Procedure.first d.encode id).comp pd)).pair
        ((Procedure.second d.encode id).comp pd)).result (by intro x; rfl)
  exact (((Procedure.casesSum left right).precompose sumView).congrEncoding
    (by rintro ⟨a,s⟩; cases a <;> rfl) (by intro x; rfl)).congrFun (by
      rintro ⟨a,s⟩
      cases a <;> rfl)

noncomputable def gateSplitter : Splitter qmaGateCodec :=
  SourcePrograms.equivSplitter _ qmaGateEquiv
    (sumSplitter _ _ (sumSplitter _ _ natural natural)
      (PrefixPrograms.pair _ _ natural natural))

noncomputable def gateInput : Procedure qmaGateCodec.encode gateCode id := by
  let left := Procedure.casesSum
    ((Procedure.sumLeft Nat.bits Nat.bits).comp EncodingPrograms.naturalInput)
    ((Procedure.sumRight Nat.bits Nat.bits).comp EncodingPrograms.naturalInput)
  let pairInput := SourcePrograms.pairInput BinaryEncoding.natural BinaryEncoding.natural natural
  let right := ((EncodingPrograms.naturalInput.comp (Procedure.first _ _)).pair
    (EncodingPrograms.naturalInput.comp (Procedure.second _ _))).comp pairInput
  let first := (Procedure.sumLeft (sumCode Nat.bits Nat.bits) (prodCode Nat.bits Nat.bits)).comp left
  let second := (Procedure.sumRight (sumCode Nat.bits Nat.bits) (prodCode Nat.bits Nat.bits)).comp right
  exact ((Procedure.casesSum first second).precompose qmaGateEquiv).result (by
    intro g
    cases g <;> rfl)

theorem gate_length_pos (g : QMAGate) : 0 < (qmaGateCodec.encode g).length := by
  cases g <;> exact Nat.succ_pos _

noncomputable def gateListSplitter : Splitter (BinaryEncoding.list qmaGateCodec) :=
  PrefixListPrograms.listSplitter qmaGateCodec gateSplitter (.hadamard 0) gate_length_pos

noncomputable def gateListInput :
    Procedure (BinaryEncoding.list qmaGateCodec).encode (listCode gateCode) id :=
  ((Procedure.listMap (.hadamard 0) (.hadamard 0) gateInput).comp
    (PrefixListPrograms.listInput qmaGateCodec gateSplitter (.hadamard 0) gate_length_pos)).congrFun
      (by intro gs; simp only [Function.comp_apply,List.map_id,id_eq])

private def tailCodec := BinaryEncoding.pair BinaryEncoding.natural
  (BinaryEncoding.list qmaGateCodec)

noncomputable def circuitTuple :
    Procedure qmaCircuitCodec.encode (prodCode BinaryEncoding.natural.encode tailCodec.encode)
      qmaCircuitEquiv :=
  (SourcePrograms.pairInput BinaryEncoding.natural tailCodec natural).precompose qmaCircuitEquiv

noncomputable def workInput : Procedure qmaCircuitCodec.encode Nat.bits QMACircuit.work :=
  EncodingPrograms.naturalInput.comp ((Procedure.first _ _).comp circuitTuple)

private noncomputable def restInput :
    Procedure qmaCircuitCodec.encode
      (prodCode BinaryEncoding.natural.encode (BinaryEncoding.list qmaGateCodec).encode)
      (fun c => (c.witness,c.gates)) :=
  (SourcePrograms.pairInput BinaryEncoding.natural (BinaryEncoding.list qmaGateCodec) natural).comp
    ((Procedure.second _ _).comp circuitTuple)

noncomputable def witnessInput : Procedure qmaCircuitCodec.encode Nat.bits QMACircuit.witness :=
  EncodingPrograms.naturalInput.comp ((Procedure.first _ _).comp restInput)

noncomputable def gatesInput : Procedure qmaCircuitCodec.encode (listCode gateCode) QMACircuit.gates :=
  gateListInput.comp ((Procedure.second _ _).comp restInput)

noncomputable def rawInput : Procedure qmaCircuitCodec.encode rawCode id :=
  (workInput.pair (witnessInput.pair gatesInput)).result (by intro c; rfl)

def cap (x : ℕ × QMACircuit) : QMACircuit :=
  ⟨min x.1 x.2.work,min x.1 x.2.witness,x.2.gates⟩

noncomputable def boundedInput :
    Procedure (prodCode unaryCode qmaCircuitCodec.encode) circuitCode cap := by
  let b := Procedure.first unaryCode qmaCircuitCodec.encode
  let c := Procedure.second unaryCode qmaCircuitCodec.encode
  let work := Procedure.clippedUnary.comp (b.pair (workInput.comp c))
  let witness := Procedure.clippedUnary.comp (b.pair (witnessInput.comp c))
  exact (work.pair (witness.pair (gatesInput.comp c))).result (by intro x; rfl)

theorem cap_eq (b : ℕ) (c : QMACircuit) (hw : c.work ≤ b) (hv : c.witness ≤ b) :
    cap (b,c)=c := by
  cases c
  simp only [cap,min_eq_right hw,min_eq_right hv]

theorem cap_eq_of_wellFormed (b : ℕ) (c : QMACircuit) (hc : c.WellFormed)
    (hw : c.work ≤ b) : cap (b,c)=c :=
  cap_eq b c hw (hc.1.trans hw)

noncomputable def workProgram : Procedure circuitCode unaryCode QMACircuit.work :=
  (Procedure.first unaryCode (prodCode unaryCode (listCode gateCode))).precompose qmaCircuitEquiv

private noncomputable def tailProgram :
    Procedure circuitCode (prodCode unaryCode (listCode gateCode))
      (fun c => (c.witness,c.gates)) :=
  (Procedure.second unaryCode (prodCode unaryCode (listCode gateCode))).precompose qmaCircuitEquiv

noncomputable def witnessProgram : Procedure circuitCode unaryCode QMACircuit.witness :=
  (Procedure.first unaryCode (listCode gateCode)).comp tailProgram

noncomputable def gatesProgram : Procedure circuitCode (listCode gateCode) QMACircuit.gates :=
  (Procedure.second unaryCode (listCode gateCode)).comp tailProgram

noncomputable def nonemptyProgram : Procedure circuitCode circuitCode qmaNonemptyCircuit := by
  let extra := Procedure.constant circuitCode (listCode gateCode)
    [QMAGate.hadamard 0,QMAGate.hadamard 0]
  let gates := (Procedure.listAppend gateCode (.hadamard 0)).comp (gatesProgram.pair extra)
  exact (workProgram.pair (witnessProgram.pair gates)).result (by intro c; rfl)

end ContinuumCoulomb.QuantumCircuitCode

end

end OAI
