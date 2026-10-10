import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumCrossingListFamily
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumCrossingScaleProgram
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumListPathStep

namespace OAI

/-! The complete rational crossing transformation, including its calibrated
scale, retained edges, mediator pairs and exact scalar shift. -/

noncomputable section
namespace ContinuumCoulomb.QuantumCrossingListLayer
open ExactQuantumFactoring.BitStackProgram MediatorListProgram
open QuantumCrossingListBlock

abbrev Input := (ℚ × QuantumListPathStep.Output) × List Crossing
def inputCode : Input → List Bool :=
  prodCode (prodCode ratCode QuantumListPathStep.outputCode) (listCode crossingCode)

def scaleInput (x : Input) : QuantumCrossingScaleProgram.Input :=
  ((x.1.1,x.1.2.2.2),(x.1.2.2.1.map (fun b => b.2.2),x.2.map Prod.fst))
def parameters (x : Input) : Parameters := (x.1.2.1,QuantumCrossingScaleProgram.value (scaleInput x))
def familyInput (x : Input) : FamilyInput := (parameters x,x.2)
def count (x : Input) : ℕ := x.1.2.1+2*x.2.length
def bonds (x : Input) : List Bond := x.1.2.2.1++family (familyInput x)
def constant (x : Input) : ℚ := x.1.2.2.2+familyOffset (familyInput x)
def value (x : Input) : QuantumListPathStep.Output := (count x,bonds x,constant x)

noncomputable opaque packetProgram : Procedure inputCode QuantumListPathStep.outputCode
    (fun x => x.1.2) :=
  (Procedure.second ratCode QuantumListPathStep.outputCode).comp
    (Procedure.first (prodCode ratCode QuantumListPathStep.outputCode) (listCode crossingCode))
noncomputable opaque nProgram : Procedure inputCode unaryCode (fun x => x.1.2.1) :=
  (Procedure.first unaryCode (prodCode (listCode bondCode) ratCode)).comp packetProgram
noncomputable opaque oldProgram : Procedure inputCode (prodCode (listCode bondCode) ratCode)
    (fun x => x.1.2.2) :=
  (Procedure.second unaryCode (prodCode (listCode bondCode) ratCode)).comp packetProgram
noncomputable opaque oldBondsProgram : Procedure inputCode (listCode bondCode)
    (fun x => x.1.2.2.1) :=
  (Procedure.first (listCode bondCode) ratCode).comp oldProgram
noncomputable opaque oldConstantProgram : Procedure inputCode ratCode
    (fun x => x.1.2.2.2) :=
  (Procedure.second (listCode bondCode) ratCode).comp oldProgram
noncomputable opaque crossingProgram : Procedure inputCode (listCode crossingCode) Prod.snd :=
  Procedure.second (prodCode ratCode QuantumListPathStep.outputCode) (listCode crossingCode)
noncomputable opaque scaleInputProgram :
    Procedure inputCode QuantumCrossingScaleProgram.inputCode scaleInput := by
  let N := (Procedure.first ratCode QuantumListPathStep.outputCode).comp
    (Procedure.first (prodCode ratCode QuantumListPathStep.outputCode) (listCode crossingCode))
  let pairs := (Procedure.listMap zeroCrossing (0,0)
    (Procedure.first (prodCode ratCode ratCode) sitesCode)).comp crossingProgram
  exact (N.pair oldConstantProgram).pair
    (((QuantumListPathStep.weightsProgram).comp oldBondsProgram).pair pairs)
noncomputable opaque parametersProgram : Procedure inputCode parametersCode parameters :=
  nProgram.pair (QuantumCrossingScaleProgram.program.comp scaleInputProgram)
noncomputable opaque familyInputProgram : Procedure inputCode familyCode familyInput :=
  parametersProgram.pair crossingProgram
noncomputable opaque countProgram : Procedure inputCode unaryCode count := by
  let r := (ExactQuantumFactoring.NativeAIG.Emission.listUnaryLength crossingCode zeroCrossing).comp crossingProgram
  exact Procedure.unaryAdd.comp (nProgram.pair
    (Procedure.unaryMul.comp ((Procedure.constant inputCode unaryCode 2).pair r)))
noncomputable opaque bondsProgram : Procedure inputCode (listCode bondCode) bonds :=
  (Procedure.listAppend bondCode zeroBond).comp
    (oldBondsProgram.pair (QuantumCrossingListBlock.familyProgram.comp familyInputProgram))
noncomputable opaque constantProgram : Procedure inputCode ratCode constant :=
  Procedure.ratAdd.comp (oldConstantProgram.pair
    (QuantumCrossingListBlock.familyOffsetProgram.comp familyInputProgram))
noncomputable opaque program : Procedure inputCode QuantumListPathStep.outputCode value :=
  countProgram.pair (bondsProgram.pair constantProgram)

theorem bonds_bounded (x : Input)
    (hb : SourceBondLists.bounded x.1.2.1 x.1.2.2.1)
    (hs : ∀ c ∈ x.2, ∀ a, site c.2 a < x.1.2.1) :
    SourceBondLists.bounded (count x) (bonds x) := by
  intro e he
  rcases List.mem_append.mp he with he | he
  · exact ⟨(hb e he).1.trans_le (Nat.le_add_right _ _),
      (hb e he).2.trans_le (Nat.le_add_right _ _)⟩
  · exact family_bounded (familyInput x) hs e he

theorem bonds_noLoops (x : Input)
    (hn : ∀ e ∈ x.1.2.2.1, e.1 ≠ e.2.1)
    (hs : ∀ c ∈ x.2, ∀ a, site c.2 a < x.1.2.1)
    (hinj : ∀ c ∈ x.2, Function.Injective (site c.2)) :
    ∀ e ∈ bonds x, e.1 ≠ e.2.1 := by
  intro e he
  rcases List.mem_append.mp he with he | he
  · exact hn e he
  · exact family_noLoops (familyInput x) hs hinj e he

def graph (x : Input) (hb : SourceBondLists.bounded x.1.2.1 x.1.2.2.1)
    (hn : ∀ e ∈ x.1.2.2.1, e.1 ≠ e.2.1)
    (hs : ∀ c ∈ x.2, ∀ a, site c.2 a < x.1.2.1)
    (hinj : ∀ c ∈ x.2, Function.Injective (site c.2)) : QMARationalExchangeGraph :=
  QuantumListGraph.ofBonds (count x) (bonds x) (constant x)
    (bonds_bounded x hb hs) (bonds_noLoops x hn hs hinj)

end ContinuumCoulomb.QuantumCrossingListLayer

end

end OAI
