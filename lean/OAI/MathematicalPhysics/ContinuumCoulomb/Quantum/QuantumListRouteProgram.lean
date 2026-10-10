import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumListScheduleProgram
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumRouteProgram
import OAI.Computability.QuantumFactoring.BitStackListIndex

namespace OAI

/-! Literal route lists accompanying the bond/work scheduler. Every new pair
is placed at the first two internal points of its selected route. -/

noncomputable section
namespace ContinuumCoulomb.QuantumListRouteProgram
open ExactQuantumFactoring.BitStackProgram QuantumRouteCode QuantumListSchedule

abbrev Routed := Entry × List Pair
def routedCode : Routed → List Bool := prodCode entryCode (listCode pairCode)
abbrev State := QuantumListSchedule.State × (List Pair × List (List Pair))
def stateCode : State → List Bool := prodCode QuantumListSchedule.stateCode
  (prodCode (listCode pairCode) (listCode (listCode pairCode)))
abbrev Input := ℚ × State
def inputCode : Input → List Bool := prodCode ratCode stateCode

def indexed (x : ℕ × Input) : Routed :=
  (((x.2.2.1.2.2.drop x.1).headD zeroEntry),((x.2.2.2.2.drop x.1).headD []))
def decorated (x : Input) : List Routed :=
  (List.range x.2.1.2.2.length).map (fun i => indexed (i,x))
def selectedRoutes (b : Bool) (x : Input) : List Routed :=
  (decorated x).filter (fun r => selected b r.1)
def lookup (p : List Pair) (i : ℕ) : Pair := (p.drop i).headD (0,0)
def freshPoints (r : Routed) : List Pair := [lookup r.2 1,lookup r.2 2]
def pathBlock (r : Routed) : List (List Pair) :=
  [[lookup r.2 1,lookup r.2 2],[lookup r.2 0,lookup r.2 1],(r.2.drop 2).reverse]
def positions (x : Input) : List Pair :=
  x.2.2.1++((selectedRoutes true x).map freshPoints).flatten
def paths (x : Input) : List (List Pair) :=
  (selectedRoutes false x).map Prod.snd++((selectedRoutes true x).map pathBlock).flatten
def value (x : Input) : State := (QuantumListSchedule.value (x.1,x.2.1),positions x,paths x)

noncomputable opaque precisionProgram : Procedure inputCode ratCode Prod.fst := Procedure.first _ _
noncomputable opaque dataProgram : Procedure inputCode stateCode Prod.snd := Procedure.second _ _
noncomputable opaque scheduleProgram : Procedure inputCode QuantumListSchedule.stateCode
    (fun x => x.2.1) := (Procedure.first _ _).comp dataProgram
noncomputable opaque spatialProgram : Procedure inputCode
    (prodCode (listCode pairCode) (listCode (listCode pairCode))) (fun x => x.2.2) :=
  (Procedure.second _ _).comp dataProgram
noncomputable opaque oldPositionsProgram : Procedure inputCode (listCode pairCode)
    (fun x => x.2.2.1) := (Procedure.first _ _).comp spatialProgram
noncomputable opaque oldPathsProgram : Procedure inputCode (listCode (listCode pairCode))
    (fun x => x.2.2.2) := (Procedure.second _ _).comp spatialProgram
noncomputable opaque entriesProgram : Procedure inputCode (listCode entryCode)
    (fun x => x.2.1.2.2) :=
  (Procedure.second _ _).comp ((Procedure.second _ _).comp scheduleProgram)
noncomputable opaque countProgram : Procedure inputCode unaryCode
    (fun x => x.2.1.2.2.length) :=
  (ExactQuantumFactoring.NativeAIG.Emission.listUnaryLength entryCode zeroEntry).comp entriesProgram

noncomputable opaque indexedProgram :
    Procedure (prodCode unaryCode inputCode) routedCode indexed := by
  let k := Procedure.unaryToBits.comp (Procedure.first unaryCode inputCode)
  let x := Procedure.second unaryCode inputCode
  exact ((Procedure.listGet entryCode zeroEntry).comp (k.pair (entriesProgram.comp x))).pair
    ((Procedure.listGet (listCode pairCode) []).comp (k.pair (oldPathsProgram.comp x)))
noncomputable opaque decoratedTabProgram :
    Procedure (prodCode unaryCode inputCode) (listCode routedCode)
      (fun x => (List.range x.1).map (fun i => indexed (i,x.2))) :=
  Procedure.tabulate (f := fun x i => indexed (i,x)) (zeroEntry,[]) indexedProgram
noncomputable opaque decoratedProgram : Procedure inputCode (listCode routedCode) decorated :=
  (decoratedTabProgram.comp (countProgram.pair (Procedure.identity inputCode))).congrFun
    (by intro x; rfl)

noncomputable opaque filterProgram (b : Bool) :
    Procedure (listCode routedCode) (listCode routedCode)
      (fun xs => xs.filter (fun r => selected b r.1)) := by
  let single := (Procedure.listCons routedCode).comp ((Procedure.identity routedCode).pair
    (Procedure.constant routedCode (listCode routedCode) []))
  let bit := (QuantumListSchedule.selectedProgram b).comp
    (Procedure.first entryCode (listCode pairCode))
  let chunk := Procedure.conditional bit single
    (Procedure.constant routedCode (listCode routedCode) [])
  refine ((QuantumRawExchange.flattenProgram routedCode (zeroEntry,[])).comp
    (Procedure.listMap (zeroEntry,[]) [] chunk)).congrFun ?_
  intro xs
  induction xs with
  | nil => rfl
  | cons r rs ih =>
    dsimp only [Function.comp_apply] at ih
    cases h : selected b r.1 <;> simpa [h] using ih
noncomputable opaque selectedProgram (b : Bool) :
    Procedure inputCode (listCode routedCode) (selectedRoutes b) :=
  (filterProgram b).comp decoratedProgram
noncomputable opaque lookupProgram (k : ℕ) :
    Procedure routedCode pairCode (fun r => lookup r.2 k) :=
  (Procedure.listGet pairCode (0,0)).comp
    ((Procedure.constant routedCode Nat.bits k).pair (Procedure.second entryCode (listCode pairCode)))

private noncomputable def pairList {α : Type} (ea : α → List Bool)
    {f g : α → Pair} (p : Procedure ea pairCode f) (q : Procedure ea pairCode g) :
    Procedure ea (listCode pairCode) (fun x => [f x,g x]) :=
  (Procedure.listCons pairCode).comp (p.pair
    ((Procedure.listCons pairCode).comp (q.pair (Procedure.constant ea (listCode pairCode) []))))
noncomputable opaque freshProgram : Procedure routedCode (listCode pairCode) freshPoints :=
  pairList routedCode (lookupProgram 1) (lookupProgram 2)
noncomputable opaque pathBlockProgram : Procedure routedCode (listCode (listCode pairCode)) pathBlock := by
  let first := freshProgram
  let second := pairList routedCode (lookupProgram 0) (lookupProgram 1)
  let third := (Procedure.listReverse pairCode (0,0)).comp
    ((Procedure.listDrop pairCode).comp
      ((Procedure.constant routedCode Nat.bits 2).pair
        (Procedure.second entryCode (listCode pairCode))))
  exact (Procedure.listCons (listCode pairCode)).comp (first.pair
    ((Procedure.listCons (listCode pairCode)).comp (second.pair
      ((Procedure.listCons (listCode pairCode)).comp
        (third.pair (Procedure.constant routedCode (listCode (listCode pairCode)) []))))))
noncomputable opaque positionsProgram : Procedure inputCode (listCode pairCode) positions :=
  (Procedure.listAppend pairCode (0,0)).comp (oldPositionsProgram.pair
    ((QuantumRawExchange.flattenProgram pairCode (0,0)).comp
      ((Procedure.listMap (zeroEntry,[]) [] freshProgram).comp (selectedProgram true))))
noncomputable opaque pathsProgram : Procedure inputCode (listCode (listCode pairCode)) paths :=
  (Procedure.listAppend (listCode pairCode) []).comp
    (((Procedure.listMap (zeroEntry,[]) [] (Procedure.second entryCode (listCode pairCode))).comp
      (selectedProgram false)).pair
      ((QuantumRawExchange.flattenProgram (listCode pairCode) []).comp
        ((Procedure.listMap (zeroEntry,[]) [] pathBlockProgram).comp (selectedProgram true))))
noncomputable opaque program : Procedure inputCode stateCode value :=
  (QuantumListSchedule.program.comp (precisionProgram.pair scheduleProgram)).pair
    (positionsProgram.pair pathsProgram)

def iterate (N : ℚ) : ℕ → State → State
  | 0,s => s
  | k+1,s => value (N,iterate N k s)
noncomputable opaque iterateProgram (k : ℕ) :
    Procedure inputCode stateCode (fun x => iterate x.1 k x.2) := by
  induction k with
  | zero => exact dataProgram
  | succ k ih => exact program.comp (precisionProgram.pair ih)

end ContinuumCoulomb.QuantumListRouteProgram

end

end OAI
