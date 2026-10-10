import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumListPathInput

namespace OAI

/-! A fixed-round routing compiler on literal bond/work lists. Each active
edge receives one singlet pair; its unfinished tail retains one less work unit. -/

noncomputable section
namespace ContinuumCoulomb.QuantumListSchedule
open ExactQuantumFactoring.BitStackProgram MediatorListProgram

abbrev Entry := ℕ × Bond
def entryCode : Entry → List Bool := prodCode unaryCode bondCode
def zeroEntry : Entry := (0,zeroBond)
def selected (active : Bool) (e : Entry) : Bool := if e.1=0 then !active else active
def partition (active : Bool) (xs : List Entry) : List Entry := xs.filter (selected active)
def erase (xs : List Entry) : List Bond := xs.map Prod.snd

noncomputable opaque selectedProgram (active : Bool) :
    Procedure entryCode Procedure.boolCode (selected active) :=
  (Procedure.conditional (Procedure.unaryZero.comp (Procedure.first unaryCode bondCode))
    (Procedure.constant entryCode Procedure.boolCode (!active))
    (Procedure.constant entryCode Procedure.boolCode active)).congrFun (by intro e; simp only [Function.comp_apply,selected,decide_eq_true_eq])

noncomputable opaque partitionProgram (active : Bool) :
    Procedure (listCode entryCode) (listCode entryCode) (partition active) := by
  let single : Procedure entryCode (listCode entryCode) (fun e => [e]) :=
    (Procedure.listCons entryCode).comp ((Procedure.identity entryCode).pair
      (Procedure.constant entryCode (listCode entryCode) []))
  let chunk := Procedure.conditional (selectedProgram active) single
    (Procedure.constant entryCode (listCode entryCode) [])
  refine ((QuantumRawExchange.flattenProgram entryCode zeroEntry).comp
    (Procedure.listMap zeroEntry [] chunk)).congrFun ?_
  intro xs
  induction xs with
  | nil => rfl
  | cons e xs ih =>
    dsimp only [Function.comp_apply] at ih
    cases h : selected active e <;> simpa [partition,h] using ih

noncomputable opaque eraseProgram : Procedure (listCode entryCode) (listCode bondCode) erase :=
  Procedure.listMap zeroEntry zeroBond (Procedure.second unaryCode bondCode)

abbrev State := ℕ × (ℚ × List Entry)
def stateCode : State → List Bool := prodCode unaryCode (prodCode ratCode (listCode entryCode))
abbrev Input := ℚ × State
def inputCode : Input → List Bool := prodCode ratCode stateCode

def stepInput (x : Input) : QuantumListPathStep.Input :=
  ((x.2.1,false,x.1,x.2.2.1),(erase (partition false x.2.2.2),erase (partition true x.2.2.2)))

noncomputable opaque stateProgram : Procedure inputCode stateCode Prod.snd := Procedure.second _ _
noncomputable opaque precisionProgram : Procedure inputCode ratCode Prod.fst := Procedure.first _ _
noncomputable opaque countInputProgram : Procedure inputCode unaryCode (fun x => x.2.1) :=
  (Procedure.first _ _).comp stateProgram
noncomputable opaque tailProgram : Procedure inputCode (prodCode ratCode (listCode entryCode))
    (fun x => x.2.2) := (Procedure.second _ _).comp stateProgram
noncomputable opaque scalarInputProgram : Procedure inputCode ratCode (fun x => x.2.2.1) :=
  (Procedure.first _ _).comp tailProgram
noncomputable opaque entriesProgram : Procedure inputCode (listCode entryCode) (fun x => x.2.2.2) :=
  (Procedure.second _ _).comp tailProgram
noncomputable opaque selectedEntriesProgram (b : Bool) :
    Procedure inputCode (listCode entryCode) (fun x => partition b x.2.2.2) :=
  (partitionProgram b).comp entriesProgram
noncomputable opaque stepInputProgram :
    Procedure inputCode QuantumListPathStep.inputCode stepInput :=
  (countInputProgram.pair ((Procedure.constant inputCode Procedure.boolCode false).pair
    (precisionProgram.pair scalarInputProgram))).pair
      ((eraseProgram.comp (selectedEntriesProgram false)).pair
        (eraseProgram.comp (selectedEntriesProgram true)))

abbrev BlockInput := QuantumListPathProgram.Parameters × (ℕ × Entry)
def blockInputCode : BlockInput → List Bool :=
  prodCode QuantumListPathProgram.parametersCode (prodCode unaryCode entryCode)
def blockBondInput (x : BlockInput) : QuantumListPathProgram.Input := (x.1,x.2.1,x.2.2.2)
def blockWork (x : BlockInput) (k : Fin 3) : ℕ := if k=2 then x.2.2.1-1 else 0
def block (x : BlockInput) : List Entry :=
  List.ofFn fun k => (blockWork x k,QuantumListPathProgram.bond (blockBondInput x) k)

noncomputable opaque blockBondInputProgram :
    Procedure blockInputCode QuantumListPathProgram.inputCode blockBondInput := by
  let p := Procedure.first QuantumListPathProgram.parametersCode (prodCode unaryCode entryCode)
  let t := Procedure.second QuantumListPathProgram.parametersCode (prodCode unaryCode entryCode)
  let i := (Procedure.first unaryCode entryCode).comp t
  let e := (Procedure.second unaryCode entryCode).comp t
  exact p.pair (i.pair ((Procedure.second unaryCode bondCode).comp e))

noncomputable opaque blockWorkProgram (k : Fin 3) :
    Procedure blockInputCode unaryCode (fun x => blockWork x k) := by
  by_cases hk : k=2
  · let p : Procedure blockInputCode unaryCode (fun x => x.2.2.1-1) :=
      Procedure.unaryPred.comp ((Procedure.first unaryCode bondCode).comp
        ((Procedure.second unaryCode entryCode).comp
          (Procedure.second QuantumListPathProgram.parametersCode (prodCode unaryCode entryCode))))
    exact p.congrFun (by intro x; simp only [blockWork,hk,ite_true])
  · exact (Procedure.constant blockInputCode unaryCode 0).congrFun
      (by intro x; simp only [blockWork,hk,ite_false])

noncomputable opaque blockProgram : Procedure blockInputCode (listCode entryCode) block :=
  QuantumRawExchange.fixedListProgram blockInputCode entryCode 3
    (fun k x => (blockWork x k,QuantumListPathProgram.bond (blockBondInput x) k))
    (fun k => (blockWorkProgram k).pair ((QuantumListPathProgram.bondProgram k).comp blockBondInputProgram))

def indexed (x : ℕ × Input) : BlockInput :=
  (QuantumListPathStep.parameters (stepInput x.2),x.1,
    ((partition true x.2.2.2.2).drop x.1).headD zeroEntry)
def family (x : Input) : List Entry :=
  ((List.range (partition true x.2.2.2).length).map (fun i => block (indexed (i,x)))).flatten

def value (x : Input) : State :=
  (QuantumListPathStep.count (stepInput x),QuantumListPathStep.constant (stepInput x),
    partition false x.2.2.2++family x)

noncomputable opaque indexedProgram :
    Procedure (prodCode unaryCode inputCode) blockInputCode indexed := by
  let i := Procedure.first unaryCode inputCode
  let x := Procedure.second unaryCode inputCode
  let p := (QuantumListPathStep.parametersProgram.comp stepInputProgram).comp x
  let xs := (selectedEntriesProgram true).comp x
  let e := (Procedure.listGet entryCode zeroEntry).comp ((Procedure.unaryToBits.comp i).pair xs)
  exact p.pair (i.pair e)

noncomputable opaque familyLengthProgram : Procedure inputCode unaryCode
    (fun x => (partition true x.2.2.2).length) :=
  (ExactQuantumFactoring.NativeAIG.Emission.listUnaryLength entryCode zeroEntry).comp
    (selectedEntriesProgram true)

noncomputable opaque familyTabProgram :
    Procedure (prodCode unaryCode inputCode) (listCode (listCode entryCode))
      (fun x => (List.range x.1).map (fun i => block (indexed (i,x.2)))) :=
  Procedure.tabulate (f := fun x i => block (indexed (i,x))) [] (blockProgram.comp indexedProgram)

noncomputable opaque familyInputProgram : Procedure inputCode (prodCode unaryCode inputCode)
    (fun x => ((partition true x.2.2.2).length,x)) :=
  familyLengthProgram.pair (Procedure.identity inputCode)

noncomputable opaque familyNestedProgram : Procedure inputCode (listCode (listCode entryCode))
    (fun x => (List.range (partition true x.2.2.2).length).map (fun i => block (indexed (i,x)))) :=
  (familyTabProgram.comp familyInputProgram).congrFun (by intro x; rfl)

noncomputable opaque familyProgram : Procedure inputCode (listCode entryCode) family :=
  (QuantumRawExchange.flattenProgram entryCode zeroEntry).comp familyNestedProgram

noncomputable opaque program : Procedure inputCode stateCode value :=
  (QuantumListPathStep.countProgram.comp stepInputProgram).pair
    ((QuantumListPathStep.constantProgram.comp stepInputProgram).pair
      ((Procedure.listAppend entryCode zeroEntry).comp
        ((selectedEntriesProgram false).pair familyProgram)))

def iterate (N : ℚ) : ℕ → State → State
  | 0,s => s
  | k+1,s => value (N,iterate N k s)

noncomputable opaque iterateProgram (k : ℕ) :
    Procedure inputCode stateCode (fun x => iterate x.1 k x.2) := by
  induction k with
  | zero => exact stateProgram
  | succ k ih => exact program.comp (precisionProgram.pair ih)

end ContinuumCoulomb.QuantumListSchedule

end

end OAI
