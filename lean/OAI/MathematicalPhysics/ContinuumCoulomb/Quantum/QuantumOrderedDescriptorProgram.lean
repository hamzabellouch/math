import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumOrderedDescriptors
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumRawFamilyProgram

namespace OAI

/-! A literal polynomial program for the exact time-grouped descriptor list. -/

noncomputable section
namespace ContinuumCoulomb.QuantumHistoryDescriptors
open ExactQuantumFactoring.BitStackProgram QuantumCircuitCode

abbrev TimeInput := QMACircuit × Descriptor
def timeCode : TimeInput → List Bool := prodCode circuitCode descriptorCode

noncomputable opaque timeValueProgram : Procedure timeCode Nat.bits
    (fun x => timeValue x.1 x.2) := by
  let c := Procedure.first circuitCode descriptorCode
  let d := Procedure.second circuitCode descriptorCode
  let tag := (Procedure.first Nat.bits Nat.bits).comp d
  let index := (Procedure.second Nat.bits Nat.bits).comp d
  let time := Procedure.unaryToBits.comp (timeProgram.comp c)
  let last := Procedure.binarySub.comp
    (time.pair (Procedure.constant timeCode Nat.bits 1))
  let test (n : ℕ) := Procedure.binaryEq.comp
    (tag.pair (Procedure.constant timeCode Nat.bits n))
  let minWithLast {f : TimeInput → ℕ} (p : Procedure timeCode Nat.bits f) :
      Procedure timeCode Nat.bits (fun x => min (f x) (x.1.gates.length-1)) :=
    (Procedure.conditional (Procedure.binaryLe.comp (p.pair last)) p last).congrFun
      (by intro x; simp only [Function.comp_apply,id_eq,decide_eq_true_eq]; split_ifs <;> omega)
  let firstUse := Procedure.unaryToBits.comp
    (QuantumFirstUseProgram.program.comp (c.pair index))
  let boundary := Procedure.conditional
    (Procedure.binaryEq.comp (index.pair (Procedure.constant timeCode Nat.bits 0)))
    (Procedure.constant timeCode Nat.bits 0) last
  exact (Procedure.conditional (test 0) (minWithLast index)
    (Procedure.conditional (test 1) boundary
    (Procedure.conditional (test 2) (minWithLast firstUse)
    (Procedure.conditional (test 3) last index)))).congrFun (by
      intro x
      simp only [timeValue,Function.comp_apply,id_eq,decide_eq_true_eq])

abbrev BucketInput := QMACircuit × ℕ
def bucketCode : BucketInput → List Bool := prodCode circuitCode Nat.bits
abbrev ChunkInput := BucketInput × Descriptor
def chunkCode : ChunkInput → List Bool := prodCode bucketCode descriptorCode

def chunk (x : ChunkInput) : List Descriptor :=
  if timeValue x.1.1 x.2=x.1.2 then [x.2] else []

noncomputable opaque chunkProgram : Procedure chunkCode (listCode descriptorCode) chunk := by
  let env := Procedure.first bucketCode descriptorCode
  let c := (Procedure.first circuitCode Nat.bits).comp env
  let t := (Procedure.second circuitCode Nat.bits).comp env
  let d := Procedure.second bucketCode descriptorCode
  let hit := Procedure.binaryEq.comp ((timeValueProgram.comp (c.pair d)).pair t)
  let nil := Procedure.constant chunkCode (listCode descriptorCode) []
  exact (Procedure.conditional hit ((Procedure.listCons descriptorCode).comp (d.pair nil))
    nil).congrFun (by intro x; simp only [chunk,Function.comp_apply,decide_eq_true_eq])

private theorem chunks_eq (c : QMACircuit) (t : ℕ) (xs : List Descriptor) :
    (xs.map (fun d => chunk ((c,t),d))).flatten =
      xs.filter (fun d => decide (timeValue c d=t)) := by
  induction xs with
  | nil => rfl
  | cons d xs ih =>
    simp only [List.map_cons,List.flatten_cons,ih,List.filter_cons]
    by_cases h : timeValue c d=t
    · simp [chunk,h]
    · simp [chunk,h]

noncomputable opaque bucketProgram : Procedure bucketCode (listCode descriptorCode)
    (fun x => bucket x.1 x.2) := by
  let chunks := (Procedure.listMapWith (f := fun e d => chunk (e,d)) (0,0) []
    chunkProgram).comp ((Procedure.identity bucketCode).pair
      (sourceProgram.comp (Procedure.first circuitCode Nat.bits)))
  exact ((QuantumRawExchange.flattenProgram descriptorCode (0,0)).comp chunks).congrFun
    (by intro x; exact chunks_eq x.1 x.2 (source x.1))

noncomputable opaque orderedEntryProgram :
    Procedure (prodCode unaryCode circuitCode) (listCode descriptorCode)
      (fun x => bucket x.2 x.1) :=
  bucketProgram.comp ((Procedure.second unaryCode circuitCode).pair
    (Procedure.unaryToBits.comp (Procedure.first unaryCode circuitCode)))

noncomputable opaque orderedProgram : Procedure circuitCode (listCode descriptorCode) ordered :=
  ((QuantumRawExchange.flattenProgram descriptorCode (0,0)).comp
    ((Procedure.tabulate (f := fun c i => bucket c i) [] orderedEntryProgram).comp
      (timeProgram.pair (Procedure.identity circuitCode)))).congrFun (by
        intro c
        simp only [ordered,List.flatMap_def,Function.comp_apply,id_eq])

noncomputable def orderedCertificate : Turing.TM2ComputableInPolyTime circuitCode
    (listCode descriptorCode) ordered := orderedProgram.toTM2

end ContinuumCoulomb.QuantumHistoryDescriptors

end

end OAI
