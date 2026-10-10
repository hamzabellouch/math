import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumListPathMatrix

namespace OAI

/-! A calibrated selected-subdivision step acting directly on finite bond
lists. The selected list order fixes the labels of every new mediator pair. -/

noncomputable section
namespace ContinuumCoulomb.QuantumListPathStep
open ExactQuantumFactoring.BitStackProgram MediatorListProgram

abbrev Input := (ℕ × (Bool × (ℚ × ℚ))) × (List Bond × List Bond)
def headCode : (ℕ × (Bool × (ℚ × ℚ))) → List Bool :=
  prodCode unaryCode (prodCode Procedure.boolCode (prodCode ratCode ratCode))
def inputCode : Input → List Bool :=
  prodCode headCode (prodCode (listCode bondCode) (listCode bondCode))
abbrev Output := ℕ × (List Bond × ℚ)
def outputCode : Output → List Bool := prodCode unaryCode (prodCode (listCode bondCode) ratCode)

def scaleInput (x : Input) : QuantumPathScaleProgram.Input :=
  (x.1.2.2,(x.2.1.map (fun e => e.2.2),x.2.2.map (fun e => e.2.2)))
def parameters (x : Input) : QuantumListPathProgram.Parameters :=
  (x.1.1,x.1.2.1,QuantumPathScaleProgram.value (scaleInput x))
def count (x : Input) : ℕ := x.1.1+x.2.2.length*2
def bonds (x : Input) : List Bond := x.2.1++QuantumListPathProgram.family (parameters x,x.2.2)
def constant (x : Input) : ℚ := x.1.2.2.2+QuantumListPathProgram.familyOffset (parameters x,x.2.2)
def value (x : Input) : Output := (count x,bonds x,constant x)

noncomputable opaque headProgram : Procedure inputCode headCode Prod.fst := Procedure.first _ _
noncomputable opaque countInputProgram : Procedure inputCode unaryCode (fun x => x.1.1) :=
  (Procedure.first _ _).comp headProgram
noncomputable opaque parityProgram : Procedure inputCode Procedure.boolCode (fun x => x.1.2.1) :=
  (Procedure.first _ _).comp ((Procedure.second _ _).comp headProgram)
noncomputable opaque constantsProgram : Procedure inputCode (prodCode ratCode ratCode)
    (fun x => x.1.2.2) :=
  (Procedure.second _ _).comp ((Procedure.second _ _).comp headProgram)
noncomputable opaque listsProgram :
    Procedure inputCode (prodCode (listCode bondCode) (listCode bondCode)) Prod.snd := Procedure.second _ _
noncomputable opaque retainedProgram : Procedure inputCode (listCode bondCode) (fun x => x.2.1) :=
  (Procedure.first _ _).comp listsProgram
noncomputable opaque selectedProgram : Procedure inputCode (listCode bondCode) (fun x => x.2.2) :=
  (Procedure.second _ _).comp listsProgram
noncomputable opaque weightProgram : Procedure bondCode ratCode (fun e => e.2.2) :=
  (Procedure.second _ _).comp (Procedure.second _ _)
noncomputable opaque weightsProgram : Procedure (listCode bondCode) (listCode ratCode)
    (fun xs => xs.map (fun e => e.2.2)) := Procedure.listMap zeroBond 0 weightProgram

noncomputable opaque scaleInputProgram :
    Procedure inputCode QuantumPathScaleProgram.inputCode scaleInput :=
  constantsProgram.pair ((weightsProgram.comp retainedProgram).pair (weightsProgram.comp selectedProgram))
noncomputable opaque parametersProgram :
    Procedure inputCode QuantumListPathProgram.parametersCode parameters :=
  countInputProgram.pair (parityProgram.pair (QuantumPathScaleProgram.program.comp scaleInputProgram))
noncomputable opaque countProgram : Procedure inputCode unaryCode count := by
  let n := (ExactQuantumFactoring.NativeAIG.Emission.listUnaryLength bondCode zeroBond).comp selectedProgram
  exact Procedure.unaryAdd.comp (countInputProgram.pair
    (Procedure.unaryMul.comp (n.pair (Procedure.constant inputCode unaryCode 2))))
noncomputable opaque familyInputProgram : Procedure inputCode QuantumListPathProgram.familyCode
    (fun x => (parameters x,x.2.2)) := parametersProgram.pair selectedProgram
noncomputable opaque bondsProgram : Procedure inputCode (listCode bondCode) bonds :=
  (Procedure.listAppend bondCode zeroBond).comp
    (retainedProgram.pair (QuantumListPathProgram.familyProgram.comp familyInputProgram))
noncomputable opaque constantProgram : Procedure inputCode ratCode constant :=
  Procedure.ratAdd.comp
    (((Procedure.second ratCode ratCode).comp constantsProgram).pair
      (QuantumListPathProgram.familyOffsetProgram.comp familyInputProgram))
noncomputable opaque program : Procedure inputCode outputCode value :=
  countProgram.pair (bondsProgram.pair constantProgram)

theorem bonds_bounded (x : Input)
    (hk : SourceBondLists.bounded x.1.1 x.2.1)
    (hs : SourceBondLists.bounded x.1.1 x.2.2) :
    SourceBondLists.bounded (count x) (bonds x) := by
  intro e he
  rcases List.mem_append.mp he with h | h
  · obtain ⟨hl,hr⟩ := hk e h
    exact ⟨hl.trans_le (Nat.le_add_right _ _),hr.trans_le (Nat.le_add_right _ _)⟩
  · exact QuantumListPathProgram.family_bounded (parameters x,x.2.2) hs e h

theorem bonds_noLoops (x : Input)
    (hk : ∀ e ∈ x.2.1, e.1 ≠ e.2.1)
    (hs : SourceBondLists.bounded x.1.1 x.2.2) : ∀ e ∈ bonds x, e.1 ≠ e.2.1 := by
  intro e he
  rcases List.mem_append.mp he with h | h
  · exact hk e h
  · exact QuantumListPathProgram.family_noLoops (parameters x,x.2.2) hs e h

def graph (x : Input) (hk : SourceBondLists.bounded x.1.1 x.2.1)
    (hs : SourceBondLists.bounded x.1.1 x.2.2) (hn : ∀ e ∈ x.2.1, e.1 ≠ e.2.1) :
    QMARationalExchangeGraph :=
  QuantumListGraph.ofBonds (count x) (bonds x) (constant x) (bonds_bounded x hk hs) (bonds_noLoops x hn hs)

end ContinuumCoulomb.QuantumListPathStep

end

end OAI
