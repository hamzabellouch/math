import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumDescriptorSites
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumOrderedDescriptorProgram
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumSupportDedup

namespace OAI

/-! Polynomial programs for the exact numeric support lists of every
time-ordered rebit term and reference edge. -/

noncomputable section
namespace ContinuumCoulomb.QuantumHistoryDescriptors
open ExactQuantumFactoring.BitStackProgram QuantumCircuitCode

private noncomputable def oneLabel {α : Type} {ea : α → List Bool} {f : α → ℕ}
    (p : Procedure ea Nat.bits f) : Procedure ea (listCode Nat.bits) (fun x => [f x]) :=
  (Procedure.listCons Nat.bits).comp
    (p.pair (Procedure.constant ea (listCode Nat.bits) []))

private noncomputable def consLabel {α : Type} {ea : α → List Bool}
    {f : α → ℕ} {g : α → List ℕ} (p : Procedure ea Nat.bits f)
    (q : Procedure ea (listCode Nat.bits) g) :
    Procedure ea (listCode Nat.bits) (fun x => f x::g x) :=
  (Procedure.listCons Nat.bits).comp (p.pair q)

noncomputable opaque distributedLabelsProgram : Procedure timeCode (listCode Nat.bits)
    (fun x => distributedLabels x.1 x.2) := by
  let c := Procedure.first circuitCode descriptorCode
  let d := Procedure.second circuitCode descriptorCode
  let tag := (Procedure.first Nat.bits Nat.bits).comp d
  let index := (Procedure.second Nat.bits Nat.bits).comp d
  let time := Procedure.unaryToBits.comp (timeProgram.comp c)
  let work := Procedure.unaryToBits.comp (workProgram.comp c)
  let const (n : ℕ) := Procedure.constant timeCode Nat.bits n
  let offset := Procedure.binaryAdd.comp (time.pair (const 2))
  let label := Procedure.binaryAdd.comp (offset.pair index)
  let fault := consLabel index (oneLabel (Procedure.successor.comp index))
  let boundary := Procedure.conditional
    (Procedure.binaryEq.comp (index.pair (const 0))) (oneLabel (const 0))
      (oneLabel (Procedure.successor.comp time))
  let firstUse := Procedure.unaryToBits.comp
    (QuantumFirstUseProgram.program.comp (c.pair index))
  let input := consLabel firstUse
    (consLabel (Procedure.successor.comp firstUse) (oneLabel label))
  let output := consLabel time (oneLabel (Procedure.binaryAdd.comp (offset.pair work)))
  let prop := QuantumHistorySiteProgram.propagationLabelsProgram.comp (c.pair index)
  let test (n : ℕ) := Procedure.binaryEq.comp (tag.pair (const n))
  exact (Procedure.conditional (test 0) fault (Procedure.conditional (test 1) boundary
    (Procedure.conditional (test 2) input (Procedure.conditional (test 3) output prop)))).congrFun
      (by intro x; simp only [distributedLabels,Function.comp_apply,id_eq,
        Nat.succ_eq_add_one,decide_eq_true_eq])

noncomputable opaque referenceWorkProgram : Procedure circuitCode Nat.bits referenceWork := by
  let time := Procedure.unaryToBits.comp timeProgram
  let work := Procedure.unaryToBits.comp workProgram
  let twice := Procedure.binaryMul.comp
    ((Procedure.constant circuitCode Nat.bits 2).pair time)
  exact Procedure.binaryAdd.comp
    ((Procedure.binaryAdd.comp (twice.pair work)).pair
      (Procedure.constant circuitCode Nat.bits 4))

abbrev ReferenceInput := QMACircuit × ℕ
def referenceCode : ReferenceInput → List Bool := prodCode circuitCode Nat.bits

noncomputable opaque orderedAtProgram : Procedure referenceCode descriptorCode
    (fun x => orderedAt x.1 x.2) :=
  (Procedure.listGet descriptorCode (0,0)).comp
    ((Procedure.second circuitCode Nat.bits).pair
      (orderedProgram.comp (Procedure.first circuitCode Nat.bits)))

noncomputable opaque rebitLabelsProgram : Procedure referenceCode (listCode Nat.bits)
    (fun x => rebitLabels x.1 x.2) := by
  let c := Procedure.first circuitCode Nat.bits
  let i := Procedure.second circuitCode Nat.bits
  let offset := Procedure.successor.comp (referenceWorkProgram.comp c)
  let labels := distributedLabelsProgram.comp (c.pair orderedAtProgram)
  let shifted := (Procedure.listMapWith (f := fun a b : ℕ => a+b) 0 0
    Procedure.binaryAdd).comp (offset.pair labels)
  exact consLabel i shifted

noncomputable opaque referenceLabelsProgram : Procedure referenceCode (listCode Nat.bits)
    (fun x => referenceLabels x.1 x.2) := by
  let c := Procedure.first circuitCode Nat.bits
  let i := Procedure.second circuitCode Nat.bits
  let cut := Procedure.successor.comp (referenceWorkProgram.comp c)
  let edge := Procedure.binarySub.comp (i.pair cut)
  let labels := consLabel edge (oneLabel (Procedure.successor.comp edge))
  exact (Procedure.conditional (Procedure.binaryLt.comp (i.pair cut)) rebitLabelsProgram
    labels).congrFun (by
      intro x
      simp only [referenceLabels,Function.comp_apply,decide_eq_true_eq])

noncomputable opaque supportLabelsProgram : Procedure referenceCode (listCode Nat.bits)
    (fun x => supportLabels x.1 x.2) := QuantumSupportDedup.program.comp referenceLabelsProgram

noncomputable def supportCertificate : Turing.TM2ComputableInPolyTime referenceCode
    (listCode Nat.bits) (fun x => supportLabels x.1 x.2) := supportLabelsProgram.toTM2

end ContinuumCoulomb.QuantumHistoryDescriptors

end

end OAI
