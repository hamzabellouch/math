import Mathlib
import OAI.Computability.MinUncut.Estimates.TM2Costed

namespace OAI

section

namespace MinUncut.Costed.GraphCodec
open _root_.Turing _root_.OAI.Turing _root_.Turing.PartrecToTM2 _root_.OAI.Turing.PartrecToTM2
open MinUncutGames.BinaryEncoding

inductive Mode | header | cell | one | zeroBit | marker | threshold | done
  deriving DecidableEq

protected abbrev Mode.enumList : List Mode := [.header, .cell, .one, .zeroBit, .marker,
  .threshold, .done]

protected theorem Mode.enumList_getElem?_ctorIdx_eq (x : Mode) :
    Mode.enumList[x.ctorIdx]? = some x := by
  cases x <;> rfl

protected theorem Mode.enumList_nodup : Mode.enumList.Nodup := by decide

instance : Fintype Mode where
  elems := ⟨Mode.enumList, Mode.enumList_nodup⟩
  complete x := by cases x <;> decide

def bitSymbol (b : Bool) : Γ' := if b then .bit1 else .bit0

def next : Mode → Γ' → Mode
  | .header,.cons => .cell
  | .threshold,.cons => .done
  | .header,_ => .header
  | .threshold,_ => .threshold
  | .done,_ => .done
  | .cell,.bit1 => .one
  | .cell,.bit0 => .zeroBit
  | .cell,_ => .cell
  | .one,_ => .cell
  | .zeroBit,.bit1 => .marker
  | .zeroBit,_ => .cell
  | .marker,.cons => .threshold
  | .marker,_ => .marker

def emit : Mode → Γ' → List Bool
  | .header,.bit0 | .threshold,.bit0 => [true,false]
  | .header,.bit1 | .threshold,.bit1 => [true,true]
  | .header,.cons | .threshold,.cons | .cell,.cons => [false]
  | .one,.cons => [true]
  | _,_ => []

def machine : FinTM2 := WordTransducer.machine .header next emit

lemma trPosNum_bits (n : PosNum) : trPosNum n=(n:ℕ).bits.map bitSymbol := by
  induction n with
  | one => simp [trPosNum,Nat.one_bits,bitSymbol]
  | bit0 n ih =>
    have hn : (n:ℕ)≠0 := ne_of_gt n.to_nat_pos
    simpa [trPosNum,PosNum.cast_bit0,← two_mul,Nat.bit0_bits _ hn,bitSymbol] using
      congrArg (List.cons Γ'.bit0) ih
  | bit1 n ih =>
    simpa [trPosNum,PosNum.cast_bit1,← two_mul,Nat.bit1_bits,bitSymbol] using
      congrArg (List.cons Γ'.bit1) ih

lemma trNat_bits (n : ℕ) : trNat n=n.bits.map bitSymbol := by
  have hh (a : Num) : trNum a=(a:ℕ).bits.map bitSymbol := by
    cases a with
    | zero => simp [trNum,Nat.zero_bits]
    | pos a => exact trPosNum_bits a
  simpa only [trNat,Num.to_of_nat] using hh (n:Num)

lemma done_output (v : List Γ') : WordTransducer.output next emit .done v=[] := by
  induction v with
  | nil => rfl
  | cons a v ih => cases a <;> simpa [WordTransducer.output,next,emit] using ih

lemma header_output (v : List Bool) (rest : List Γ') :
    WordTransducer.output next emit .header (v.map bitSymbol++Γ'.cons::rest)=
      frame v++WordTransducer.output next emit .cell rest := by
  induction v with
  | nil => rfl
  | cons b v ih =>
    cases b <;> simp [WordTransducer.output,next,emit,bitSymbol,frame,ih]

lemma threshold_output (v : List Bool) (rest : List Γ') :
    WordTransducer.output next emit .threshold (v.map bitSymbol++Γ'.cons::rest)=frame v := by
  induction v with
  | nil => simp [WordTransducer.output,next,emit,frame,done_output]
  | cons b v ih =>
    cases b <;> simp [WordTransducer.output,next,emit,bitSymbol,frame,ih]

lemma cells_output (v : List Bool) (k : ℕ) (rest : List ℕ) :
    WordTransducer.output next emit .cell (trList (v.map Bool.toNat++2::k::rest))=
      v++nameBits k := by
  induction v with
  | nil =>
    change WordTransducer.output next emit .cell
      ([.bit0,.bit1,.cons]++(trNat k++Γ'.cons::trList rest))=nameBits k
    simp only [List.cons_append,List.nil_append,WordTransducer.output,next,emit]
    rw [trNat_bits,threshold_output]
    rfl
  | cons b v ih =>
    cases b with
    | false =>
      change false::WordTransducer.output next emit .cell
        (trList (v.map Bool.toNat++2::k::rest))=false::(v++nameBits k)
      exact congrArg (List.cons false) ih
    | true =>
      change true::WordTransducer.output next emit .cell
        (trList (v.map Bool.toNat++2::k::rest))=true::(v++nameBits k)
      exact congrArg (List.cons true) ih

lemma output (n k : ℕ) (v : List Bool) (rest : List ℕ) :
    WordTransducer.output next emit .header (trList (n::(v.map Bool.toNat++2::k::rest)))=
      nameBits n++v++nameBits k := by
  rw [trList,trNat_bits,header_output,cells_output]
  simp only [nameBits,List.append_assoc]

lemma finiteAlphabet (k : machine.K) : Finite (machine.Γ k) :=
  WordTransducer.finiteAlphabet _ _ _ k

def outputsInTime (n k : ℕ) (v : List Bool) (rest : List ℕ) :
    TM2OutputsInTime machine (trList (n::(v.map Bool.toNat++2::k::rest)))
      (some (nameBits n++v++nameBits k))
      (2*bitsize (n::(v.map Bool.toNat++2::k::rest))+
        (nameBits n++v++nameBits k).length+2) := by
  have hh := WordTransducer.outputsInTime .header next emit (trList (n::(v.map Bool.toNat++2::k::rest)))
  exact (congrArg (fun w : List Bool =>
    TM2OutputsInTime machine (trList (n :: (v.map Bool.toNat ++ 2 :: k :: rest)))
      (some w) (2 * bitsize (n :: (v.map Bool.toNat ++ 2 :: k :: rest)) + w.length + 2))
    (output n k v rest)).mp hh

end MinUncut.Costed.GraphCodec

end

end OAI
