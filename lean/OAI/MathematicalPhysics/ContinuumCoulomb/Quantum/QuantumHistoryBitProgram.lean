import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumSupportLookup
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumAlgebraicScalarProgram

namespace OAI

/-! Literal bit reads for the small history tables, and a bounded Boolean
scan.  The register bound is unary; this scan has no spin-configuration loop. -/

noncomputable section
namespace ContinuumCoulomb.QuantumHistoryBitProgram
open ExactQuantumFactoring.BitStackProgram QuantumAlgebraicScalar

abbrev Data := List ℕ × (List ℕ × List ℕ)
def dataCode : Data → List Bool :=
  prodCode (listCode Nat.bits) (prodCode (listCode Nat.bits) (listCode Nat.bits))
abbrev Query := ℕ × Data
def queryCode : Query → List Bool := prodCode Nat.bits dataCode

def bit (n : ℕ) : Fin 2 := ⟨n % 2,Nat.mod_lt _ (by decide)⟩

def row (d : Data) (q : ℕ) : Fin 2 :=
  bit (QuantumSupportLookup.value (q,d.1,d.2.1))

def column (d : Data) (q : ℕ) : Fin 2 :=
  bit (QuantumSupportLookup.value (q,d.1,d.2.2))

def readPair (x : Query) : ℕ × ℕ := ((row x.2 x.1).val,(column x.2 x.1).val)

noncomputable opaque rowProgram : Procedure queryCode Nat.bits (fun x => (row x.2 x.1).val) := by
  let q := Procedure.first Nat.bits dataCode
  let d := Procedure.second Nat.bits dataCode
  let labels := (Procedure.first (listCode Nat.bits)
    (prodCode (listCode Nat.bits) (listCode Nat.bits))).comp d
  let values := (Procedure.second (listCode Nat.bits)
    (prodCode (listCode Nat.bits) (listCode Nat.bits))).comp d
  let s := (Procedure.first (listCode Nat.bits) (listCode Nat.bits)).comp values
  exact Procedure.binaryMod.comp
    ((QuantumSupportLookup.program.comp (q.pair (labels.pair s))).pair
      (Procedure.constant queryCode Nat.bits 2))

noncomputable opaque columnProgram :
    Procedure queryCode Nat.bits (fun x => (column x.2 x.1).val) := by
  let q := Procedure.first Nat.bits dataCode
  let d := Procedure.second Nat.bits dataCode
  let labels := (Procedure.first (listCode Nat.bits)
    (prodCode (listCode Nat.bits) (listCode Nat.bits))).comp d
  let values := (Procedure.second (listCode Nat.bits)
    (prodCode (listCode Nat.bits) (listCode Nat.bits))).comp d
  let t := (Procedure.second (listCode Nat.bits) (listCode Nat.bits)).comp values
  exact Procedure.binaryMod.comp
    ((QuantumSupportLookup.program.comp (q.pair (labels.pair t))).pair
      (Procedure.constant queryCode Nat.bits 2))

noncomputable opaque readPairProgram :
    Procedure queryCode (prodCode Nat.bits Nat.bits) readPair :=
  rowProgram.pair columnProgram

theorem bit_as_test (n : ℕ) : bit n = if n % 2 = 0 then 0 else 1 := by
  apply Fin.ext
  have hn := Nat.mod_lt n (by decide : 0 < 2)
  by_cases h : n % 2 = 0
  · simp [bit,h]
  · have he : n % 2 = 1 := by omega
    simp [bit,he]

def matrixEntry (A : Fin 2 → Fin 2 → Scalar) (x : ℕ × ℕ) : Scalar :=
  A (bit x.1) (bit x.2)

noncomputable opaque matrixEntryProgram (A : Fin 2 → Fin 2 → Scalar) :
    Procedure (prodCode Nat.bits Nat.bits) scalarCode (matrixEntry A) := by
  let l := Procedure.first Nat.bits Nat.bits
  let r := Procedure.second Nat.bits Nat.bits
  let two := Procedure.constant (prodCode Nat.bits Nat.bits) Nat.bits 2
  let zero := Procedure.constant (prodCode Nat.bits Nat.bits) Nat.bits 0
  let bl := Procedure.binaryEq.comp ((Procedure.binaryMod.comp (l.pair two)).pair zero)
  let br := Procedure.binaryEq.comp ((Procedure.binaryMod.comp (r.pair two)).pair zero)
  exact ((Procedure.ofBool₂ scalarCode
    (fun b c => A (if b then 0 else 1) (if c then 0 else 1))).comp
      (bl.pair br)).congrFun (by
        intro x
        simp only [Function.comp_apply,decide_eq_true_eq,matrixEntry,bit_as_test])

def allBits (xs : List Bool) : Bool := xs.all id

private theorem fold_and (xs : List Bool) (b : Bool) :
    xs.foldl (fun a c => c && a) b = (b && xs.all id) := by
  induction xs generalizing b with
  | nil => simp
  | cons c xs ih =>
    simp only [List.foldl_cons,List.all_cons,id_eq,ih]
    cases b <;> cases c <;> rfl

noncomputable opaque allProgram :
    Procedure (listCode Procedure.boolCode) Procedure.boolCode allBits := by
  let p := Procedure.foldList false Procedure.boolAnd (Polynomial.C 1) (by
    intro xs b i
    norm_num [Procedure.boolCode])
  exact (p.comp ((Procedure.identity (listCode Procedure.boolCode)).pair
    (Procedure.constant (listCode Procedure.boolCode) Procedure.boolCode true))).congrFun
      (by intro xs; simp only [Function.comp_apply,id_eq,fold_and,Bool.true_and,allBits])

theorem row_actual (c : QMACircuit) (hT : 0 < c.gates.length)
    (a : QMAReferenceTerm (qmaHistoryReferenceWork c))
    (s t : Fin (QuantumOrderedSupport.sites c hT a).length → Fin 2)
    (q : QuantumOrderedSupport.Qubit c) :
    row (QuantumOrderedSupport.encodedSites c hT a,
      QuantumSupportLookup.supportBits c hT a s,
      QuantumSupportLookup.supportBits c hT a t)
      (QuantumOrderedSupport.siteNumber c q) =
    qmaSupportExtend ((qmaOrderedHistoryModel c hT).sites a)
      (fun i => s ((QuantumOrderedSupport.supportEquiv c hT a).symm i)) q :=
  QuantumSupportLookup.support_readBit c hT a s q

theorem column_actual (c : QMACircuit) (hT : 0 < c.gates.length)
    (a : QMAReferenceTerm (qmaHistoryReferenceWork c))
    (s t : Fin (QuantumOrderedSupport.sites c hT a).length → Fin 2)
    (q : QuantumOrderedSupport.Qubit c) :
    column (QuantumOrderedSupport.encodedSites c hT a,
      QuantumSupportLookup.supportBits c hT a s,
      QuantumSupportLookup.supportBits c hT a t)
      (QuantumOrderedSupport.siteNumber c q) =
    qmaSupportExtend ((qmaOrderedHistoryModel c hT).sites a)
      (fun i => t ((QuantumOrderedSupport.supportEquiv c hT a).symm i)) q :=
  QuantumSupportLookup.support_readBit c hT a t q

end ContinuumCoulomb.QuantumHistoryBitProgram

end

end OAI
