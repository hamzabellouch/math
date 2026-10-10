import Mathlib
import OAI.Computability.MinUncut.Graphs.GraphWordCodec
import OAI.Computability.MinUncut.Estimates.FiberPrefix

namespace OAI

section
namespace MinUncut.Costed.FrameDecode
open _root_.Turing _root_.OAI.Turing _root_.Turing.PartrecToTM2 _root_.OAI.Turing.PartrecToTM2 MinUncutGames.BinaryEncoding
inductive Mode
  | flag | payload | suffix
  deriving DecidableEq

protected abbrev Mode.enumList : List Mode := [.flag, .payload, .suffix]

protected theorem Mode.enumList_getElem?_ctorIdx_eq (x : Mode) :
    Mode.enumList[x.ctorIdx]? = some x := by
  cases x <;> rfl

protected theorem Mode.enumList_nodup : Mode.enumList.Nodup := by decide

instance : Fintype Mode where
  elems := ⟨Mode.enumList, Mode.enumList_nodup⟩
  complete x := by cases x <;> decide

def next : Mode → Bool → Mode
  | .flag,true => .payload
  | .flag,false => .suffix
  | .payload,_ => .flag
  | .suffix,_ => .suffix

def symbol (b : Bool) : ℕ := b.toNat+1

def emit : Mode → Bool → List Γ'
  | .flag,true => []
  | .flag,false => [.cons]
  | .payload,b => [GraphCodec.bitSymbol b]
  | .suffix,b => trNat (symbol b)++[.cons]

def machine : FinTM2 := WordTransducer.machine .flag next emit
lemma finiteAlphabet (k : machine.K) : Finite (machine.Γ k) :=
  WordTransducer.finiteAlphabet .flag next emit k
lemma suffix_output (v : List Bool) :
    WordTransducer.output next emit .suffix v=trList (v.map symbol) := by
  induction v with
  | nil => rfl
  | cons b v ih =>
    simp only [WordTransducer.output,next,emit,List.map_cons,trList,ih,List.append_assoc,List.singleton_append]
lemma frame_output (v w : List Bool) :
    WordTransducer.output next emit .flag (frame v++w)=
      v.map GraphCodec.bitSymbol++Γ'.cons::trList (w.map symbol) := by
  induction v with
  | nil => simpa only [frame,List.cons_append,List.nil_append,WordTransducer.output,next,emit,
      List.singleton_append,List.map_nil] using congrArg (List.cons Γ'.cons) (suffix_output w)
  | cons b v ih =>
    simp only [frame,List.cons_append,WordTransducer.output,next,emit,List.nil_append,
      List.map_cons,ih]
lemma output_spec (K : ℕ) (w : List Bool) :
    WordTransducer.output next emit .flag (nameBits K++w)=trList (K::w.map symbol) := by
  rw [nameBits,frame_output,←GraphCodec.trNat_bits]
  rfl
def outputs (K : ℕ) (w : List Bool) :
    TM2OutputsInTime machine (nameBits K++w) (some (trList (K::w.map symbol)))
      (2*(nameBits K++w).length+(trList (K::w.map symbol)).length+2) := by
  have h := WordTransducer.outputsInTime .flag next emit (nameBits K++w)
  erw [output_spec] at h
  exact h
lemma count_symbols (v : List Bool) : UnaryWords.count (v.map symbol)=v.length := by
  induction v with
  | nil => rfl
  | cons b v ih =>
    simp only [List.map_cons,UnaryWords.count,symbol,show b.toNat+1≠0 by omega,ite_false,ih,List.length_cons]
lemma magnitude_symbols (v : List Bool) : magnitude (v.map symbol)≤3*v.length := by
  induction v with
  | nil => rfl
  | cons b v ih =>
    have hb : b.toNat≤1 := by cases b <;> decide
    simp only [List.map_cons,magnitude_cons,List.length_cons,symbol]
    omega
end MinUncut.Costed.FrameDecode

end

end OAI
