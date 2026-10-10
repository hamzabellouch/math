import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumOrderedLabelPacking
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumOrderedRawPackingProgram

namespace OAI

/-! The literal six-local sparse-word compiler followed by the rational
four-spin compiler.  Its only input is a precision, a unary qubit count,
and the ordered rational sparse-word list. -/

noncomputable section
namespace ContinuumCoulomb.QuantumOrderedLabelCompile
open ExactQuantumFactoring.BitStackProgram QuantumOrderedLabelFamily
open QuantumOrderedLabelTable
open scoped Classical

abbrev Input := QuantumOrderedLabelFamily.Input

def qubitCount (x : Input) : ℕ := 4*(QuantumOrderedLabelPipeline.output x).1

def classify (xs : List Entry) : List QuantumRawExchange.Raw :=
  xs.map QuantumOrderedRawPacking.value

def labelEntries (x : Input) : List Entry := (QuantumOrderedLabelPipeline.output x).2

def rawEntries : Input → List QuantumRawExchange.Raw := classify ∘ labelEntries

def outputCount : Input → ℕ := Prod.fst ∘ QuantumOrderedLabelPipeline.output

def rawInput (x : Input) : QuantumRawExchange.ScheduleInput :=
  (outputCount x,x.1,rawEntries x)

def output : Input → List MediatorListProgram.Bond × ℚ :=
  QuantumRawExchange.compile ∘ rawInput

noncomputable opaque classifyProgram : Procedure (listCode entryCode)
    (listCode QuantumRawExchange.rawCode) classify := by
  let p := Procedure.listMap ([],0) QuantumRawExchange.zeroRaw QuantumOrderedRawPacking.program
  exact p.congrEncoding (by intro xs; rfl) (by intro ys; rfl)

noncomputable opaque labelEntriesProgram : Procedure inputCode (listCode entryCode)
    labelEntries :=
  (Procedure.second unaryCode (listCode entryCode)).comp
    QuantumOrderedLabelPipeline.outputProgram

noncomputable opaque rawEntriesProgram : Procedure inputCode
    (listCode QuantumRawExchange.rawCode) rawEntries :=
  Procedure.comp (f := labelEntries) (g := classify) classifyProgram labelEntriesProgram

noncomputable opaque outputCountProgram : Procedure inputCode unaryCode outputCount :=
  (Procedure.first unaryCode (listCode entryCode)).comp QuantumOrderedLabelPipeline.outputProgram

noncomputable opaque outputProgram : Procedure inputCode
    (prodCode (listCode MediatorListProgram.bondCode) ratCode) output := by
  let input : Procedure inputCode QuantumRawExchange.scheduleCode rawInput :=
    outputCountProgram.pair
      ((Procedure.unaryToBits.comp precisionProgram).pair rawEntriesProgram)
  exact QuantumRawExchange.compileProgram.comp input

noncomputable def certificate : Turing.TM2ComputableInPolyTime inputCode
    (prodCode (listCode MediatorListProgram.bondCode) ratCode) output := outputProgram.toTM2

variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
variable {m n : ℕ}

def finalSites (xs : κ → List ι) (w : κ → ι → Fin 4) :=
  QuantumOrderedPrivate.outputSites (QuantumOrderedXZ.sites xs w)

def finalWord (xs : κ → List ι) (w : κ → ι → Fin 4) :=
  QuantumOrderedPrivate.outputWord (QuantumOrderedXZ.sites xs w) (QuantumOrderedXZ.word xs w)

def finalCoefficient (J : κ → ℚ) (N : ℕ) :=
  QuantumOrderedPrivate.outputCoefficient (QuantumOrderedXZ.coefficient J N) N

theorem output_table (q : Fin n ≃ ι) (e : Fin m ≃ κ)
    (xs : κ → List ι) (w : κ → ι → Fin 4) (J : κ → ℚ)
    (hlen : ∀ a, (xs a).length ≤ 6) (hx : ∀ a, (xs a).Nodup) (N : ℕ) :
    output (N,n,table e (index q) xs w J) =
      QuantumOrderedRawBlock.output N
        (numberedSites (qubits6 q e) (terms6 e) (finalSites xs w))
        (numberedWord (qubits6 q e) (terms6 e) (finalWord xs w))
        (fun i => finalCoefficient J N (terms6 e i)) := by
  unfold output rawInput outputCount rawEntries labelEntries classify
  simp only [Function.comp_apply]
  simp only [QuantumOrderedLabelTable.output_table q e xs w J hlen hx N]
  rw [packed_table]
  rfl

omit [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] in
theorem qubitCount_table (q : Fin n ≃ ι) (e : Fin m ≃ κ)
    (xs : κ → List ι) (w : κ → ι → Fin 4) (J : κ → ℚ) (N : ℕ) :
    qubitCount (N,n,table e (index q) xs w J)=4*(n+3717*m) := by
  rw [qubitCount,QuantumOrderedLabelPipeline.output_qubits]
  simp only [table,List.length_ofFn]

end ContinuumCoulomb.QuantumOrderedLabelCompile

end

end OAI
