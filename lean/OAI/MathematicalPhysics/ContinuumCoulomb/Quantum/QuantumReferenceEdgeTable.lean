import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumRebitLocal
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumRebitDiagonal
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumFixedMatrixProgram

namespace OAI

/-! Exact local tables for the reference-chain edges.  Their only nontrivial
entry is the fixed two-spin expression (I-Y tensor Y)/2. -/

noncomputable section
namespace ContinuumCoulomb.QuantumReferenceEdgeTable
open QuantumAlgebraicScalar QuantumAlgebraicHistory QuantumHistoryDiagonal
open QuantumHistoryBitProgram QuantumFixedPauli
open ExactQuantumFactoring.BitStackProgram
open scoped Classical

abbrev Input := ℕ × List ℕ
def inputCode : Input → List Bool := prodCode Nat.bits (listCode Nat.bits)

def data (n : ℕ) (s t : Fin n → Fin 2) (x : Input) : Data :=
  (x.2,List.ofFn (fun j => (s j).val),List.ofFn (fun j => (t j).val))

def table (n : ℕ) (x : Input) : Matrix (Fin n → Fin 2) (Fin n → Fin 2) Scalar :=
  fun s t => mul (rat (1/2)) (sub (identity s t)
    (mul (QuantumFixedPauli.pauli 2 (row (data n s t x) x.1) (column (data n s t x) x.1))
      (QuantumFixedPauli.pauli 2 (row (data n s t x) (x.1+1))
        (column (data n s t x) (x.1+1)))))

noncomputable opaque dataProgram (n : ℕ) (s t : Fin n → Fin 2) :
    Procedure inputCode dataCode (data n s t) :=
  (Procedure.second Nat.bits (listCode Nat.bits)).pair
    ((Procedure.constant inputCode (listCode Nat.bits) (List.ofFn (fun j => (s j).val))).pair
      (Procedure.constant inputCode (listCode Nat.bits) (List.ofFn (fun j => (t j).val))))

private theorem bit_val (b : Fin 2) : QuantumHistoryBitProgram.bit b.val=b := by
  apply Fin.ext
  exact Nat.mod_eq_of_lt b.isLt

noncomputable opaque entryProgram (n : ℕ) (s t : Fin n → Fin 2) :
    Procedure inputCode scalarCode (fun x => table n x s t) := by
  let index := Procedure.first Nat.bits (listCode Nat.bits)
  let evaluate (p : Procedure inputCode Nat.bits (fun x => x.1)) :=
    (matrixEntryProgram (QuantumFixedPauli.pauli 2)).comp
      (readPairProgram.comp (p.pair (dataProgram n s t)))
  let left := evaluate index
  let right := (matrixEntryProgram (QuantumFixedPauli.pauli 2)).comp
    (readPairProgram.comp ((Procedure.successor.comp index).pair (dataProgram n s t)))
  exact (mulProgram.comp ((Procedure.constant inputCode scalarCode (rat (1/2))).pair
    (subProgram.comp ((Procedure.constant inputCode scalarCode (identity s t)).pair
      (mulProgram.comp (left.pair right)))))).congrFun (by
    intro x
    simp only [table,Function.comp_apply,readPair,matrixEntry,Nat.succ_eq_add_one,bit_val])

noncomputable def tableProgram (n : ℕ) : Procedure inputCode matrixCode
    (fun x => matrixData (table n x)) :=
  QuantumFixedMatrix.dataProgram (β := Fin n → Fin 2) inputCode (table n)
    (QuantumReferenceEdgeTable.entryProgram n)

theorem inactive (c : QMACircuit) (hT : 0<c.gates.length)
    (i : Fin (qmaHistoryReferenceWork c))
    (s : Fin (QuantumOrderedSupport.sites c hT (.inr i)).length → Fin 2)
    (q : QuantumOrderedSupport.Qubit c)
    (hq : q≠.inl i.castSucc ∧ q≠.inl i.succ) :
    orderedExtend c hT (.inr i) s q=0 := by
  have hn : q∉(qmaOrderedHistoryModel c hT).sites (.inr i) := by
    change q∉{Sum.inl i.castSucc,Sum.inl i.succ}
    intro hm
    rcases Finset.mem_insert.mp hm with h | h
    · exact hq.1 h
    · exact hq.2 (Finset.mem_singleton.mp h)
  exact dite_eq_right hn

theorem ordered_entry (c : QMACircuit) (hT : 0<c.gates.length)
    (i : Fin (qmaHistoryReferenceWork c))
    (s t : Fin (QuantumOrderedSupport.sites c hT (.inr i)).length → Fin 2) :
    orderedTable c hT (.inr i) s t=
      table (QuantumOrderedSupport.sites c hT (.inr i)).length
        (i.val,QuantumOrderedSupport.encodedSites c hT (.inr i)) s t := by
  let S := orderedExtend c hT (.inr i) s
  let T := orderedExtend c hT (.inr i) t
  have hd : S ∘ Sum.inr=T ∘ Sum.inr := by
    funext q
    exact (inactive c hT i s (.inr q) (by simp)).trans
      (inactive c hT i t (.inr q) (by simp)).symm
  have hr : S ∘ Sum.inl=T ∘ Sum.inl ↔ s=t := by
    constructor
    · intro h
      apply orderedExtend_injective c hT (.inr i)
      funext q
      cases q with
      | inl j => exact congrFun h j
      | inr j => exact congrFun hd j
    · rintro rfl
      rfl
  have hs : ∀ k, k≠i.castSucc → k≠i.succ → S (.inl k)=T (.inl k) := by
    intro k hk hl
    exact (inactive c hT i s (.inl k) (by simpa only [ne_eq,Sum.inl.injEq] using And.intro hk hl)).trans
      (inactive c hT i t (.inl k) (by simpa only [ne_eq,Sum.inl.injEq] using And.intro hk hl)).symm
  have hb (u : Fin (QuantumOrderedSupport.sites c hT (.inr i)).length → Fin 2)
      (v : Fin (QuantumOrderedSupport.sites c hT (.inr i)).length → Fin 2)
      (j : Fin (qmaHistoryReferenceWork c+1)) :
      row (data _ u v (i.val,QuantumOrderedSupport.encodedSites c hT (.inr i))) j.val=
        orderedExtend c hT (.inr i) u (.inl j) :=
    QuantumHistoryBitProgram.row_actual c hT (.inr i) u v (.inl j)
  have hc (j : Fin (qmaHistoryReferenceWork c+1)) :
      column (data _ s t (i.val,QuantumOrderedSupport.encodedSites c hT (.inr i))) j.val=
        T (.inl j) :=
    QuantumHistoryBitProgram.column_actual c hT (.inr i) s t (.inl j)
  change referenceEdge (qmaHistoryReferenceWork c) i S T=_
  unfold referenceEdge pairY
  simp only [identity,hd,hr,Function.comp_apply,ite_true]
  rw [ite_eq_left hs]
  unfold table
  have hbl := hb s t i.castSucc
  have hbr := hb s t i.succ
  have hcl := hc i.castSucc
  have hcr := hc i.succ
  simp only [Fin.val_castSucc,Fin.val_succ] at hbl hbr hcl hcr
  dsimp only [Prod.fst]
  rw [hbl,hcl,hbr,hcr]
  apply value_injective
  simp only [identity,value_mul,value_sub,value_rat,Rat.cast_one,mul_one]
  rfl

theorem table_actual (c : QMACircuit) (hT : 0<c.gates.length)
    (i : Fin (qmaHistoryReferenceWork c)) :
    table (QuantumOrderedSupport.sites c hT (.inr i)).length
        (i.val,QuantumOrderedSupport.encodedSites c hT (.inr i))=
      orderedTable c hT (.inr i) := by
  funext s t
  exact (ordered_entry c hT i s t).symm

end ContinuumCoulomb.QuantumReferenceEdgeTable

end

end OAI
