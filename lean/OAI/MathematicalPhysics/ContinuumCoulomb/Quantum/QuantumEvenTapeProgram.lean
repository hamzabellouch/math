import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumPlanarTapeProgram
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumEvenListPieces
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumListSchedule

namespace OAI

/-! One literal even subdivision, with its reserved leaf and odd route tails. -/

noncomputable section
namespace ContinuumCoulomb.QuantumEvenTapeProgram
open ExactQuantumFactoring.BitStackProgram QuantumRouteCode MediatorListProgram

abbrev Input := ℚ × QuantumPlanarTapeProgram.Output
def inputCode : Input → List Bool := prodCode ratCode QuantumPlanarTapeProgram.outputCode
def stepInput (x : Input) : QuantumListPathStep.Input :=
  ((x.2.1.1,true,x.1,x.2.1.2.2),([],x.2.1.2.1))
def route (x : Input) (i : ℕ) : List Pair := (x.2.2.2.drop i).headD []
def blockInput (x : ℕ × Input) : QuantumListSchedule.BlockInput :=
  (QuantumListPathStep.parameters (stepInput x.2),x.1,
    4*((route x.2 x.1).length-1),(x.2.2.1.2.1.drop x.1).headD zeroBond)
def entries (x : Input) : List QuantumListSchedule.Entry :=
  ((List.range x.2.1.2.1.length).map (fun i => QuantumListSchedule.block (blockInput (i,x)))).flatten
def positions (x : Input) : List Pair :=
  x.2.2.1.map qmaLeafCenter++(x.2.2.2.map QuantumEvenListPieces.fresh).flatten
def paths (x : Input) : List (List Pair) := (x.2.2.2.map QuantumEvenListPieces.paths).flatten
def value (x : Input) : QuantumListRouteProgram.State :=
  ((QuantumListPathStep.count (stepInput x),QuantumListPathStep.constant (stepInput x),entries x),
    positions x,paths x)

noncomputable opaque precisionProgram : Procedure inputCode ratCode Prod.fst := Procedure.first _ _
noncomputable opaque dataProgram : Procedure inputCode QuantumPlanarTapeProgram.outputCode Prod.snd :=
  Procedure.second _ _
noncomputable opaque packetProgram : Procedure inputCode QuantumListPathStep.outputCode
    (fun x => x.2.1) := (Procedure.first _ _).comp dataProgram
noncomputable opaque geometryProgram : Procedure inputCode
    (prodCode (listCode pairCode) (listCode (listCode pairCode))) (fun x => x.2.2) :=
  (Procedure.second _ _).comp dataProgram
noncomputable opaque countProgram : Procedure inputCode unaryCode (fun x => x.2.1.1) :=
  (Procedure.first _ _).comp packetProgram
noncomputable opaque bondsProgram : Procedure inputCode (listCode bondCode) (fun x => x.2.1.2.1) :=
  ((Procedure.first (listCode bondCode) ratCode).comp
    (Procedure.second unaryCode (prodCode (listCode bondCode) ratCode))).comp packetProgram
noncomputable opaque constantProgram : Procedure inputCode ratCode (fun x => x.2.1.2.2) :=
  ((Procedure.second (listCode bondCode) ratCode).comp
    (Procedure.second unaryCode (prodCode (listCode bondCode) ratCode))).comp packetProgram
noncomputable opaque oldPositionsProgram : Procedure inputCode (listCode pairCode)
    (fun x => x.2.2.1) := (Procedure.first _ _).comp geometryProgram
noncomputable opaque oldPathsProgram : Procedure inputCode (listCode (listCode pairCode))
    (fun x => x.2.2.2) := (Procedure.second _ _).comp geometryProgram
noncomputable opaque stepInputProgram : Procedure inputCode QuantumListPathStep.inputCode stepInput :=
  (countProgram.pair ((Procedure.constant inputCode Procedure.boolCode true).pair
    (precisionProgram.pair constantProgram))).pair
      ((Procedure.constant inputCode (listCode bondCode) []).pair bondsProgram)

noncomputable opaque routeProgram : Procedure (prodCode unaryCode inputCode) (listCode pairCode)
    (fun x => route x.2 x.1) :=
  (Procedure.listGet (listCode pairCode) []).comp
    ((Procedure.unaryToBits.comp (Procedure.first unaryCode inputCode)).pair
      (oldPathsProgram.comp (Procedure.second unaryCode inputCode)))
noncomputable opaque workProgram : Procedure (prodCode unaryCode inputCode) unaryCode
    (fun x => 4*((route x.2 x.1).length-1)) :=
  Procedure.unaryMul.comp ((Procedure.constant _ unaryCode 4).pair
    (Procedure.unaryPred.comp
      ((ExactQuantumFactoring.NativeAIG.Emission.listUnaryLength pairCode (0,0)).comp routeProgram)))
noncomputable opaque blockInputProgram : Procedure (prodCode unaryCode inputCode)
    QuantumListSchedule.blockInputCode blockInput := by
  let i := Procedure.first unaryCode inputCode
  let x := Procedure.second unaryCode inputCode
  let b := (Procedure.listGet bondCode zeroBond).comp
    ((Procedure.unaryToBits.comp i).pair (bondsProgram.comp x))
  let p := (QuantumListPathStep.parametersProgram.comp stepInputProgram).comp x
  exact p.pair (i.pair (workProgram.pair b))
noncomputable opaque blockProgram : Procedure (prodCode unaryCode inputCode)
    (listCode QuantumListSchedule.entryCode)
    (fun x => QuantumListSchedule.block (blockInput x)) :=
  QuantumListSchedule.blockProgram.comp blockInputProgram
noncomputable opaque entriesTabProgram : Procedure (prodCode unaryCode inputCode)
    (listCode (listCode QuantumListSchedule.entryCode))
    (fun x => (List.range x.1).map (fun i => QuantumListSchedule.block (blockInput (i,x.2)))) :=
  Procedure.tabulate (f := fun x i => QuantumListSchedule.block (blockInput (i,x))) [] blockProgram
noncomputable opaque bondCountProgram : Procedure inputCode unaryCode
    (fun x => x.2.1.2.1.length) :=
  (ExactQuantumFactoring.NativeAIG.Emission.listUnaryLength bondCode zeroBond).comp bondsProgram
noncomputable opaque entriesNestedProgram : Procedure inputCode
    (listCode (listCode QuantumListSchedule.entryCode))
    (fun x => (List.range x.2.1.2.1.length).map
      (fun i => QuantumListSchedule.block (blockInput (i,x)))) :=
  (entriesTabProgram.comp (bondCountProgram.pair (Procedure.identity inputCode))).congrFun
    (by intro x; rfl)
noncomputable opaque entriesProgram : Procedure inputCode
    (listCode QuantumListSchedule.entryCode) entries :=
  ((QuantumRawExchange.flattenProgram QuantumListSchedule.entryCode QuantumListSchedule.zeroEntry).comp
    entriesNestedProgram).congrFun (by intro x; rfl)

noncomputable opaque positionsProgram : Procedure inputCode (listCode pairCode) positions :=
  (Procedure.listAppend pairCode (0,0)).comp
    (((Procedure.listMap (0,0) (0,0) QuantumRouteLeafCode.centerProgram).comp oldPositionsProgram).pair
      ((QuantumRawExchange.flattenProgram pairCode (0,0)).comp
        ((Procedure.listMap [] [] QuantumEvenListPieces.freshProgram).comp oldPathsProgram)))
noncomputable opaque pathsProgram : Procedure inputCode (listCode (listCode pairCode)) paths :=
  (QuantumRawExchange.flattenProgram (listCode pairCode) []).comp
    ((Procedure.listMap [] [] QuantumEvenListPieces.pathsProgram).comp oldPathsProgram)
noncomputable opaque program : Procedure inputCode QuantumListRouteProgram.stateCode value :=
  (((QuantumListPathStep.countProgram.comp stepInputProgram).pair
    ((QuantumListPathStep.constantProgram.comp stepInputProgram).pair entriesProgram)).pair
      (positionsProgram.pair pathsProgram))

theorem erase_entries (x : Input) :
    QuantumListSchedule.erase (entries x)=QuantumListPathStep.bonds (stepInput x) := by
  unfold entries
  simp only [QuantumListSchedule.erase,List.map_flatten,List.map_map]
  change ((List.range x.2.1.2.1.length).map (fun i =>
    QuantumListSchedule.erase (QuantumListSchedule.block (blockInput (i,x))))).flatten=_
  simp_rw [QuantumListSchedule.erase_block]
  rfl

theorem value_valid (x : Input)
    (hb : SourceBondLists.bounded x.2.1.1 x.2.1.2.1) : QuantumListSchedule.Valid (value x).1 := by
  have hk : SourceBondLists.bounded x.2.1.1 ([] : List Bond) := by simp [SourceBondLists.bounded]
  have hkn : ∀ e ∈ ([] : List Bond), e.1≠e.2.1 := by simp
  constructor
  · change SourceBondLists.bounded (QuantumListPathStep.count (stepInput x))
      (QuantumListSchedule.erase (entries x))
    rw [erase_entries]
    exact QuantumListPathStep.bonds_bounded (stepInput x) hk hb
  · change ∀ e ∈ QuantumListSchedule.erase (entries x), e.1≠e.2.1
    rw [erase_entries]
    exact QuantumListPathStep.bonds_noLoops (stepInput x) hkn hb

theorem value_energy_error (x : Input)
    (hb : SourceBondLists.bounded x.2.1.1 x.2.1.2.1)
    (hn : ∀ e ∈ x.2.1.2.1, e.1≠e.2.1) (hN : 0<x.1) :
    |QuantumListSchedule.energy (value x).1-
      sourceMatrixBottom x.2.1.1 (SourceBondLists.matrix x.2.1.1 x.2.1.2.1+
        (x.2.1.2.2:ℂ) • 1)| ≤ 1/(x.1:ℝ) := by
  have hk : SourceBondLists.bounded x.2.1.1 ([] : List Bond) := by simp [SourceBondLists.bounded]
  have hkn : ∀ e ∈ ([] : List Bond), e.1≠e.2.1 := by simp
  have h := QuantumListPathStep.energy_error_input (stepInput x) hk hb hkn hn hN
  change |sourceMatrixBottom (QuantumListPathStep.count (stepInput x))
    (SourceBondLists.matrix (QuantumListPathStep.count (stepInput x))
      (QuantumListSchedule.erase (entries x))+
        (QuantumListPathStep.constant (stepInput x):ℂ) • 1)-_|≤_
  rw [erase_entries]
  exact h

end ContinuumCoulomb.QuantumEvenTapeProgram

end

end OAI
