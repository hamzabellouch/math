import Mathlib
import OAI.Combinatorics.MatchingCount.Machines.TableLookup

namespace OAI

namespace MatchingFPRAS.TreeData

def bits (A : List Bool) : Data := ofList (A.map bit)
@[simp] lemma bits_nil : bits []=.nil := rfl
@[simp] lemma bits_cons (b : Bool) (A : List Bool) : bits (b::A)=.cons (bit b) (bits A) := rfl
lemma bits_length (A : List Bool) : (encode (bits A)).length≤4*A.length+1 := by
  induction A with
  | nil => simp [encode]
  | cons b A ih => cases b <;> simp only [bits_cons,encode,bit,Bool.false_eq_true,↓reduceIte,
      List.length_cons,List.length_append,List.length_nil] <;> omega
end MatchingFPRAS.TreeData

namespace MatchingFPRAS.TreeBits
open Turing MachineCost RegisterProc TreeData TreeTransfer

def decodeProgram : Unit→TM2.Stmt (fun _ : Fin 3=>Bool) Unit (Option Bool) := fun _=>
  .pop 0 (fun _ x=>x) (.branch (fun x=>x.getD false)
    (.pop 0 (fun _ x=>x) (.branch (fun x=>x.getD false)
      (.pop 0 (fun v _=>v) (.pop 0 (fun v _=>v) (.push 1 (fun _=>true) (.goto (fun _=>())))))
      (.push 1 (fun _=>false) (.goto (fun _=>())))))
    (.load (fun _=>none) .halt))
lemma decode_nil (A B C : List Bool) (v : Option Bool) :
    advance (TM2.step decodeProgram) (cfg (some ()) (false::A) B C v)=cfg none A B C none := by
  simp [advance,TM2.step,decodeProgram,TM2.stepAux,cfg,update_zero]
lemma decode_cons (b : Bool) (bs A B C : List Bool) (v : Option Bool) :
    advance (TM2.step decodeProgram) (cfg (some ()) (encode (bits (b::bs))++A) B C v)=
      cfg (some ()) (encode (bits bs)++A) (b::B) C (some b) := by
  cases b <;> simp [advance,TM2.step,decodeProgram,TM2.stepAux,cfg,update_zero,update_one,encode,bit]
lemma run_decode (bs A B C : List Bool) (v : Option Bool) :
    MachineCost.run (TM2.step decodeProgram) (bs.length+1)
      (cfg (some ()) (encode (bits bs)++A) B C v)=cfg none A (bs.reverse++B) C none := by
  induction bs generalizing B v with
  | nil => simpa only [bits_nil,encode,List.singleton_append,List.length_nil,List.reverse_nil,List.nil_append,Nat.zero_add,MachineCost.run] using decode_nil A B C v
  | cons b bs ih =>
    rw [List.length_cons,Nat.add_right_comm,MachineCost.run,decode_cons,ih]
    simp only [List.reverse_cons,List.append_assoc,List.singleton_append]
def decodeRaw : Proc (Fin 3) := ⟨Unit,decodeProgram⟩
lemma decodeRaw_exec (bs A B C : List Bool) :
    Exec decodeRaw ![encode (bits bs)++A,B,C] ![A,bs.reverse++B,C] (bs.length+1) :=
  ⟨_,le_rfl,run_decode bs A B C none⟩

def encodeProgram : Unit→TM2.Stmt (fun _ : Fin 3=>Bool) Unit (Option Bool) := fun _=>
  .pop 0 (fun _ x=>x) (.branch Option.isNone (.load (fun _=>none) .halt)
    (.branch (fun x=>x.getD false)
      (.push 1 (fun _=>false) (.push 1 (fun _=>false) (.push 1 (fun _=>true) (.push 1 (fun _=>true) (.goto (fun _=>()))))))
      (.push 1 (fun _=>false) (.push 1 (fun _=>true) (.goto (fun _=>()))))))
lemma encode_nil (B C : List Bool) (v : Option Bool) :
    advance (TM2.step encodeProgram) (cfg (some ()) [] B C v)=cfg none [] B C none := by
  simp [advance,TM2.step,encodeProgram,TM2.stepAux,cfg,update_zero]
lemma encode_cons (b : Bool) (bs C : List Bool) (x : Data) (v : Option Bool) :
    advance (TM2.step encodeProgram) (cfg (some ()) (b::bs) (encode x) C v)=
      cfg (some ()) bs (encode (.cons (bit b) x)) C (some b) := by
  cases b <;> simp [advance,TM2.step,encodeProgram,TM2.stepAux,cfg,update_zero,update_one,encode,bit]
def prepend (bs : List Bool) (x : Data) : Data := bs.foldr (fun b x=>.cons (bit b) x) x
lemma prepend_append (A B : List Bool) (x : Data) : prepend (A++B) x=prepend A (prepend B x) := by
  simp [prepend,List.foldr_append]
lemma run_encode (bs C : List Bool) (x : Data) (v : Option Bool) :
    MachineCost.run (TM2.step encodeProgram) (bs.length+1)
      (cfg (some ()) bs (encode x) C v)=cfg none [] (encode (prepend bs.reverse x)) C none := by
  induction bs generalizing x v with
  | nil => exact encode_nil (encode x) C v
  | cons b bs ih =>
    rw [List.length_cons,Nat.add_right_comm,MachineCost.run,encode_cons,ih,List.reverse_cons,prepend_append]
    rfl
lemma prepend_bits (bs : List Bool) : prepend bs .nil=bits bs := by
  induction bs <;> simp_all [prepend,bits,ofList]
def encodeRaw : Proc (Fin 3) := ⟨Unit,encodeProgram⟩
lemma encodeRaw_exec (bs C : List Bool) :
    Exec encodeRaw ![bs.reverse,[false],C] ![[],encode (bits bs),C] (bs.length+1) := by
  refine ⟨_,le_rfl,?_⟩
  have h:=run_encode bs.reverse C .nil none
  simpa only [List.length_reverse,List.reverse_reverse,prepend_bits,encode,encodeRaw,cfg,stackData] using h
end MatchingFPRAS.TreeBits

end OAI
