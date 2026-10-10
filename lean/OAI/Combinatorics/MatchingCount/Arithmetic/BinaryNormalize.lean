import Mathlib
import OAI.Combinatorics.MatchingCount.Machines.TreeMachine

namespace OAI

namespace MatchingFPRAS.BinaryNormalize
open Turing MachineCost RegisterProc TreeTransfer
open StackAddition (value value_bits)

def normalize (A : List Bool) : List Bool := (A.reverse.dropWhile Bool.not).reverse
lemma normalize_nil : normalize []=[] := rfl
lemma normalize_cons (b : Bool) (A : List Bool) :
    normalize (b::A)=if normalize A=[] ∧ b=false then [] else b::normalize A := by
  simp only [normalize,List.reverse_cons,List.dropWhile_append]
  have hh (B : List Bool) :
      (if B.isEmpty then [b].dropWhile Bool.not else B++[b]).reverse=
        if B.reverse=[] ∧ b=false then [] else b::B.reverse := by
    cases B <;> cases b <;> simp
  exact hh _
lemma normalize_bits (A : List Bool) : normalize A=(value A).bits := by
  induction A with
  | nil => rfl
  | cons b A ih =>
    rw [normalize_cons,ih]
    cases b with
    | false =>
      by_cases hz : value A=0
      · simp [hz,value]
      · have hne : (value A).bits≠[] := by
          intro emptyBits
          exact hz ((value_bits (value A)).symm.trans (congrArg value emptyBits))
        simp only [value,Bool.toNat_false,Nat.zero_add, Nat.bit0_bits _ hz,hne,false_and,↓reduceIte]
    | true =>
      simp only [Bool.true_eq_false,and_false,↓reduceIte,value,Bool.toNat_true]
      rw [Nat.add_comm 1 (2*value A),Nat.bit1_bits]
lemma normalize_length (A : List Bool) : (normalize A).length≤A.length := by
  simpa only [normalize,List.length_reverse] using List.length_dropWhile_le Bool.not A.reverse

def stripProgram : Unit→TM2.Stmt (fun _ : Fin 3=>Bool) Unit (Option Bool) := fun _=>
  .peek 0 (fun _ x=>x) (.branch (fun x=>x.isNone || x.getD false)
    (.load (fun _=>none) .halt)
    (.pop 0 (fun v _=>v) (.goto (fun _=>()))))
lemma strip_nil (B C : List Bool) (v : Option Bool) :
    advance (TM2.step stripProgram) (cfg (some ()) [] B C v)=cfg none [] B C none := by
  simp [advance,TM2.step,stripProgram,TM2.stepAux,cfg]
lemma strip_true (A B C : List Bool) (v : Option Bool) :
    advance (TM2.step stripProgram) (cfg (some ()) (true::A) B C v)=cfg none (true::A) B C none := by
  simp [advance,TM2.step,stripProgram,TM2.stepAux,cfg]
lemma strip_false (A B C : List Bool) (v : Option Bool) :
    advance (TM2.step stripProgram) (cfg (some ()) (false::A) B C v)=cfg (some ()) A B C (some false) := by
  simp [advance,TM2.step,stripProgram,TM2.stepAux,cfg,update_zero]
lemma run_strip (A B C : List Bool) (v : Option Bool) :
    ∃ n≤A.length+1,MachineCost.run (TM2.step stripProgram) n (cfg (some ()) A B C v)=
      cfg none (A.dropWhile Bool.not) B C none := by
  induction A generalizing v with
  | nil => exact ⟨1,le_rfl,strip_nil B C v⟩
  | cons a A ih => cases a with
    | false =>
      obtain ⟨n,hn,he⟩:=ih (some false)
      refine ⟨n+1,by simp only [List.length_cons]; omega,?_⟩
      rw [MachineCost.run,strip_false,he]
      rfl
    | true => exact ⟨1,by simp,strip_true A B C v⟩
def stripRaw : Proc (Fin 3) := ⟨Unit,stripProgram⟩
lemma stripRaw_exec (A B C : List Bool) :
    Exec stripRaw ![A,B,C] ![A.dropWhile Bool.not,B,C] (A.length+1) := run_strip A B C none

def swap01 : Fin 3 ↪ Fin 3 := triple 1 0 2 (by decide) (by decide) (by decide)
lemma reindex_swap (P : Proc (Fin 3)) (A B C A' B' C' : List Bool) (n : ℕ)
    (h : Exec P ![A,B,C] ![A',B',C'] n) :
    Exec (reindex P swap01) ![B,A,C] ![B',A',C'] n := by
  have hh:=exec_on P (1 : Fin 3) 0 2 (by decide) (by decide) (by decide) ![B,A,C] A' B' C' n h
  have hout : put3 ![B,A,C] (1 : Fin 3) 0 2 A' B' C'=![B',A',C'] := by
    funext i; fin_cases i <;> simp [put3]
  rw [hout] at hh
  exact hh

def program : Proc (Fin 3) := seq reverseRaw (seq (reindex stripRaw swap01) (reindex reverseRaw swap01))
theorem exec (A C : List Bool) : Exec program ![A,[],C] ![normalize A,[],C] (3*A.length+3) := by
  have h₁:=reverseRaw_exec A [] C
  simp only [List.append_nil] at h₁
  have h₂:=reindex_swap stripRaw A.reverse [] C _ [] C _ (stripRaw_exec A.reverse [] C)
  have h₃:=reindex_swap reverseRaw (A.reverse.dropWhile Bool.not) [] C [] _ C _
    (reverseRaw_exec (A.reverse.dropWhile Bool.not) [] C)
  simp only [List.append_nil] at h₃
  have hh:=h₁.seq (h₂.seq h₃)
  apply hh.mono
  have hl:=List.length_dropWhile_le Bool.not A.reverse
  simp only [List.length_reverse] at hl ⊢
  omega
end MatchingFPRAS.BinaryNormalize

end OAI
