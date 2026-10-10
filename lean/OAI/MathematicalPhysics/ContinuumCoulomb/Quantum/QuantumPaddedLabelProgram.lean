import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumPaddedLabelData
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumPaddedSampling
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumOrderedLabelFamily

namespace OAI

/-! Fixed-arity local history packets: sparse numeric labels and sampled
algebraic coefficients share exactly the same fixed Pauli-word order. -/

noncomputable section
namespace ContinuumCoulomb.QuantumPaddedLabelProgram
open QuantumAlgebraicScalar QuantumFixedPauli QuantumPaddedHistory
open QuantumOrderedLabelData
open ExactQuantumFactoring.BitStackProgram
open scoped Classical

abbrev Input := ℕ × (List ℕ × List Scalar)
def inputCode : Input → List Bool :=
  prodCode unaryCode (prodCode (listCode Nat.bits) matrixCode)

def labels (n m : ℕ) (w : Fin (n+m) → Fin 4) (xs : List ℕ) : List Letter :=
  List.ofFn (fun i : Fin n => ((xs.drop i.val).headD 0,
    (QuantumPaddedPauli.paddedWord n m w i).val))

def entry (n m : ℕ) (w : Fin (n+m) → Fin 4) (x : Input) : QuantumOrderedLabelFamily.Entry :=
  (labels n m w x.2.1,sample x.1 (QuantumPaddedTable.coefficient n m x.2.2 w))

def packet (n m : ℕ) (x : Input) : List QuantumOrderedLabelFamily.Entry :=
  (enumerate (Fin (n+m) → Fin 4)).map (fun w => entry n m w x)

noncomputable opaque precisionProgram : Procedure inputCode unaryCode Prod.fst := Procedure.first _ _
noncomputable opaque indicesProgram : Procedure inputCode (listCode Nat.bits) (fun x => x.2.1) :=
  (Procedure.first _ _).comp (Procedure.second _ _)
noncomputable opaque matrixProgram : Procedure inputCode matrixCode (fun x => x.2.2) :=
  (Procedure.second _ _).comp (Procedure.second _ _)

noncomputable def labelsProgram (n m : ℕ) (w : Fin (n+m) → Fin 4) :
    Procedure (listCode Nat.bits) labelsCode (labels n m w) :=
  QuantumRawExchange.fixedListProgram (listCode Nat.bits) labelCode n _ (fun i =>
    ((Procedure.listGet Nat.bits 0).comp
      ((Procedure.constant (listCode Nat.bits) Nat.bits i.val).pair
        (Procedure.identity (listCode Nat.bits)))).pair
      (Procedure.constant (listCode Nat.bits) Nat.bits
        (QuantumPaddedPauli.paddedWord n m w i).val))

noncomputable opaque entryProgram (n m : ℕ) (w : Fin (n+m) → Fin 4) :
    Procedure inputCode QuantumOrderedLabelFamily.entryCode (entry n m w) :=
  ((labelsProgram n m w).comp indicesProgram).pair
    (sampleProgram.comp (precisionProgram.pair
      ((QuantumPaddedTable.coefficientProgram n m w).comp matrixProgram)))

noncomputable def packetProgram (n m : ℕ) :
    Procedure inputCode (listCode QuantumOrderedLabelFamily.entryCode) (packet n m) :=
  (QuantumRawExchange.fixedListProgram inputCode QuantumOrderedLabelFamily.entryCode
    (Fintype.card (Fin (n+m) → Fin 4))
    (fun i x => entry n m ((Fintype.equivFin (Fin (n+m) → Fin 4)).symm i) x)
    (fun i => entryProgram n m ((Fintype.equivFin (Fin (n+m) → Fin 4)).symm i))).congrFun
      (by intro x; simp only [packet,enumerate,List.map_ofFn,Function.comp_def])

def uniformPacket (x : Input) : List QuantumOrderedLabelFamily.Entry :=
  if x.2.1.length=0 then packet 0 6 x else
  if x.2.1.length=1 then packet 1 5 x else
  if x.2.1.length=2 then packet 2 4 x else
  if x.2.1.length=3 then packet 3 3 x else
  if x.2.1.length=4 then packet 4 2 x else
  if x.2.1.length=5 then packet 5 1 x else packet 6 0 x

noncomputable opaque uniformProgram : Procedure inputCode
    (listCode QuantumOrderedLabelFamily.entryCode) uniformPacket := by
  let count := Procedure.unaryToBits.comp
    ((ExactQuantumFactoring.NativeAIG.Emission.listUnaryLength Nat.bits 0).comp indicesProgram)
  let test (n : ℕ) := Procedure.binaryEq.comp
    (count.pair (Procedure.constant inputCode Nat.bits n))
  exact (Procedure.conditional (test 0) (packetProgram 0 6)
    (Procedure.conditional (test 1) (packetProgram 1 5)
    (Procedure.conditional (test 2) (packetProgram 2 4)
    (Procedure.conditional (test 3) (packetProgram 3 3)
    (Procedure.conditional (test 4) (packetProgram 4 2)
    (Procedure.conditional (test 5) (packetProgram 5 1) (packetProgram 6 0))))))).congrFun
      (by intro x; simp only [uniformPacket,Function.comp_apply,id_eq,decide_eq_true_eq])

theorem uniformPacket_eq (x : Input) (h : x.2.1.length ≤ 6) :
    uniformPacket x=packet x.2.1.length (6-x.2.1.length) x := by
  generalize hn : x.2.1.length=n at *
  interval_cases n <;> simp only [uniformPacket,hn] <;> norm_num

theorem packet_length (n m : ℕ) (x : Input) :
    (packet n m x).length=4^(n+m) := by
  simp only [packet,List.length_map,enumerate,List.length_ofFn,Fintype.card_fun,
    Fintype.card_fin]

theorem uniformPacket_length (x : Input) (h : x.2.1.length ≤ 6) :
    (uniformPacket x).length=4096 := by
  rw [uniformPacket_eq x h,packet_length,Nat.add_sub_of_le h]
  norm_num

noncomputable def certificate : Turing.TM2ComputableInPolyTime inputCode
    (listCode QuantumOrderedLabelFamily.entryCode) uniformPacket := uniformProgram.toTM2

end ContinuumCoulomb.QuantumPaddedLabelProgram

end

end OAI
