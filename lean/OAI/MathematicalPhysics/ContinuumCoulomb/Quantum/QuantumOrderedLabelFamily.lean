import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumOrderedLabelProgram
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumOrderedWeightProgram

namespace OAI

/-! A literal indexed list stage, shared by the six fixed local reductions.
New mediator indices are the old qubit count plus the input term index.
Unary counts bound the output size; rational coefficients stay binary. -/

noncomputable section
namespace ContinuumCoulomb.QuantumOrderedLabelFamily
open ExactQuantumFactoring.BitStackProgram
open QuantumOrderedLabelData

abbrev Entry := List Letter × ℚ
abbrev State := ℕ × List Entry
abbrev Input := ℕ × State
abbrev BlockInput := (ℕ × ℚ) × Entry

def entryCode : Entry → List Bool := prodCode labelsCode ratCode
def stateCode : State → List Bool := prodCode unaryCode (listCode entryCode)
def inputCode : Input → List Bool := prodCode unaryCode stateCode
def blockCode : BlockInput → List Bool := prodCode (prodCode Nat.bits ratCode) entryCode

def weights (x : Input) : QuantumOrderedWeightProgram.Input := (x.1,x.2.2.map Prod.snd)
def radius (x : Input) : ℚ := QuantumOrderedWeightProgram.scale (weights x)
def indexed (x : ℕ × Input) : BlockInput :=
  ((x.2.2.1+x.1,radius x.2),(x.2.2.2.drop x.1).headD ([],0))

def block (d : ℕ) (f : ℕ → List Letter → Fin d → List Letter)
    (g : ℚ → ℚ → Fin d → ℚ) (x : BlockInput) : List Entry :=
  List.ofFn (fun k => (f x.1.1 x.2.1 k,g x.1.2 x.2.2 k))

def family (d : ℕ) (f : ℕ → List Letter → Fin d → List Letter)
    (g : ℚ → ℚ → Fin d → ℚ) (x : Input) : List Entry :=
  ((List.range x.2.2.length).map (fun i => block d f g (indexed (i,x)))).flatten

def value (d : ℕ) (f : ℕ → List Letter → Fin d → List Letter)
    (g : ℚ → ℚ → Fin d → ℚ) (x : Input) : State :=
  (x.2.1+x.2.2.length,family d f g x)

noncomputable opaque stateProgram : Procedure inputCode stateCode Prod.snd := Procedure.second _ _
noncomputable opaque precisionProgram : Procedure inputCode unaryCode Prod.fst := Procedure.first _ _
noncomputable opaque countProgram : Procedure inputCode unaryCode (fun x => x.2.1) :=
  (Procedure.first _ _).comp stateProgram
noncomputable opaque entriesProgram : Procedure inputCode (listCode entryCode) (fun x => x.2.2) :=
  (Procedure.second _ _).comp stateProgram
noncomputable opaque lengthProgram : Procedure inputCode unaryCode (fun x => x.2.2.length) :=
  (ExactQuantumFactoring.NativeAIG.Emission.listUnaryLength entryCode ([],0)).comp entriesProgram
noncomputable opaque weightsProgram : Procedure inputCode QuantumOrderedWeightProgram.inputCode weights :=
  precisionProgram.pair ((Procedure.listMap ([],0) 0
    (Procedure.second labelsCode ratCode)).comp entriesProgram)
noncomputable opaque radiusProgram : Procedure inputCode ratCode radius :=
  QuantumOrderedWeightProgram.scaleProgram.comp weightsProgram

noncomputable opaque indexedProgram : Procedure (prodCode unaryCode inputCode) blockCode indexed := by
  let i := Procedure.first unaryCode inputCode
  let x := Procedure.second unaryCode inputCode
  let n := (Procedure.unaryToBits.comp countProgram).comp x
  let j := Procedure.unaryToBits.comp i
  let selected :=  (Procedure.listGet entryCode ([],0)).comp (j.pair (entriesProgram.comp x))
  exact ((Procedure.binaryAdd.comp (n.pair j)).pair (radiusProgram.comp x)).pair selected

noncomputable def blockProgram (d : ℕ)
    (f : ℕ → List Letter → Fin d → List Letter) (g : ℚ → ℚ → Fin d → ℚ)
    (pf : ∀ k, Procedure QuantumOrderedLabelData.blockCode labelsCode (fun x => f x.1 x.2 k))
    (pg : ∀ k, Procedure QuantumOrderedWeightProgram.pairCode ratCode (fun x => g x.1 x.2 k)) :
    Procedure blockCode (listCode entryCode) (block d f g) := by
  let params := Procedure.first (prodCode Nat.bits ratCode) entryCode
  let entry := Procedure.second (prodCode Nat.bits ratCode) entryCode
  let mediator := (Procedure.first Nat.bits ratCode).comp params
  let scale := (Procedure.second Nat.bits ratCode).comp params
  let labels := (Procedure.first labelsCode ratCode).comp entry
  let coefficient := (Procedure.second labelsCode ratCode).comp entry
  exact QuantumRawExchange.fixedListProgram blockCode entryCode d _
    (fun k => ((pf k).comp (mediator.pair labels)).pair
      ((pg k).comp (scale.pair coefficient)))

noncomputable def familyProgram (d : ℕ)
    (f : ℕ → List Letter → Fin d → List Letter) (g : ℚ → ℚ → Fin d → ℚ)
    (p : Procedure blockCode (listCode entryCode) (block d f g)) :
    Procedure inputCode (listCode entryCode) (family d f g) := by
  let tab := Procedure.tabulate (f := fun x i => block d f g (indexed (i,x))) []
    (p.comp indexedProgram)
  exact (QuantumRawExchange.flattenProgram entryCode ([],0)).comp
    (tab.comp (lengthProgram.pair (Procedure.identity inputCode)))

noncomputable def valueProgram (d : ℕ)
    (f : ℕ → List Letter → Fin d → List Letter) (g : ℚ → ℚ → Fin d → ℚ)
    (p : Procedure blockCode (listCode entryCode) (block d f g)) :
    Procedure inputCode stateCode (value d f g) :=
  (Procedure.unaryAdd.comp (countProgram.pair lengthProgram)).pair (familyProgram d f g p)

theorem family_length (d : ℕ)
    (f : ℕ → List Letter → Fin d → List Letter) (g : ℚ → ℚ → Fin d → ℚ)
    (x : Input) : (family d f g x).length=x.2.2.length*d := by
  unfold family
  rw [List.length_flatten,List.map_map]
  simp only [Function.comp_def,block,List.length_ofFn]
  simp

end ContinuumCoulomb.QuantumOrderedLabelFamily

end

end OAI
