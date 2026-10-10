import Mathlib
import OAI.Combinatorics.MatchingCount.Arithmetic.TreeMultiply
import OAI.Combinatorics.MatchingCount.Arithmetic.TreeCompare
import OAI.Combinatorics.MatchingCount.Arithmetic.TreeSubtract
import OAI.Combinatorics.MatchingCount.Arithmetic.BinaryDivision

namespace OAI

namespace MatchingFPRAS.TreeDivision
open TreeData TreeMachine RegisterProc
open StackAddition (value value_bits)
open BinaryDivision (low nextQ nextR)
open RegisterControl (Effect)

abbrev Reg := Fin 7
inductive Point where
  | loop | split | shift | copyR | copyD | cmp | test | copyD2 | sub | one | zero | pushQ | halt
  deriving DecidableEq, Inhabited
instance : Fintype Point := ⟨{.loop,.split,.shift,.copyR,.copyD,.cmp,.test,.copyD2,.sub,.one,.zero,.pushQ,.halt},
  by intro p; cases p <;> simp⟩
def program : Point → RegisterControl.Instr Reg Point
  | .loop => .branch 0 .halt .split
  | .split => .call (procedure (TreeMachine.Instr.split (Λ:=Unit) 4 0 (by decide) ())) .shift
  | .shift => .call (procedure (TreeMachine.Instr.cons (Λ:=Unit) 4 2 (by decide) ())) .copyR
  | .copyR => .call (procedure (TreeMachine.Instr.copy (Λ:=Unit) 2 4 (by decide) ())) .copyD
  | .copyD => .call (procedure (TreeMachine.Instr.copy (Λ:=Unit) 1 5 (by decide) ())) .cmp
  | .cmp => .call (TreeArithmetic.less 4 5 (by decide)) .test
  | .test => .branch 4 .copyD2 .zero
  | .copyD2 => .call (procedure (TreeMachine.Instr.copy (Λ:=Unit) 1 5 (by decide) ())) .sub
  | .sub => .call (TreeArithmetic.sub 2 5 (by decide)) .one
  | .one => .call (procedure (TreeMachine.Instr.cons (Λ:=Unit) 5 4 (by decide) ())) .pushQ
  | .zero => .call (procedure (TreeMachine.Instr.nil (Λ:=Unit) 4 ())) .pushQ
  | .pushQ => .call (procedure (TreeMachine.Instr.cons (Λ:=Unit) 4 3 (by decide) ())) .loop
  | .halt => .halt

def splitState (E : Env Reg) (b : Bool) (A : List Bool) := putPair E 4 0 (bit b) (bits A)
def shiftState (E : Env Reg) (b : Bool) (A C : List Bool) :=
  putPair (splitState E b A) 4 2 .nil (bits (b::C))
def copyState (E : Env Reg) (b : Bool) (A B C : List Bool) :=
  putPair (putPair (shiftState E b A C) 2 4 (bits (b::C)) (bits (b::C))) 1 5 (bits B) (bits B)
def tested (E : Env Reg) (b : Bool) (A B C : List Bool) :=
  putPair (copyState E b A B C) 4 5 (bit (low b B C)) .nil
def reduced (E : Env Reg) (b : Bool) (A B C : List Bool) :=
  putPair (putPair (tested E b A B C) 1 5 (bits B) (bits B)) 2 5
    (nat (value (b::C)-value B)) .nil
def digitState (E : Env Reg) (b : Bool) (A B C : List Bool) : Env Reg :=
  if low b B C then Function.update (tested E b A B C) 4 .nil
  else putPair (reduced E b A B C) 5 4 .nil (bit true)
def next (E : Env Reg) (b : Bool) (A B Q C : List Bool) : Env Reg :=
  putPair (digitState E b A B C) 4 3 .nil (bits (nextQ b B Q C))
def result (E : Env Reg) : List Bool → List Bool → List Bool → List Bool → Env Reg
  | [],_,_,_ => E
  | b::A,B,Q,C => result (next E b A B Q C) A B (nextQ b B Q C) (nextR b B C)

lemma next_zero (E : Env Reg) (b : Bool) (A B Q C : List Bool) : next E b A B Q C 0=bits A := by
  unfold next digitState
  split_ifs <;> simp [tested,copyState,shiftState,splitState,reduced,putPair]
lemma next_one (E : Env Reg) (b : Bool) (A B Q C : List Bool) : next E b A B Q C 1=bits B := by
  unfold next digitState
  split_ifs <;> simp [tested,copyState,reduced,putPair]
lemma next_two (E : Env Reg) (b : Bool) (A B Q C : List Bool) :
    next E b A B Q C 2=bits (nextR b B C) := by
  unfold next digitState nextR
  split_ifs <;> simp [tested,copyState,shiftState,splitState,reduced,putPair,nat,bits]
lemma next_three (E : Env Reg) (b : Bool) (A B Q C : List Bool) :
    next E b A B Q C 3=bits (nextQ b B Q C) := by simp [next,putPair]
lemma next_four (E : Env Reg) (b : Bool) (A B Q C : List Bool) : next E b A B Q C 4=.nil := by
  simp [next,putPair]
lemma next_five (E : Env Reg) (b : Bool) (A B Q C : List Bool) : next E b A B Q C 5=.nil := by
  unfold next digitState
  split_ifs <;> simp [tested,reduced,putPair]
lemma next_six (E : Env Reg) (b : Bool) (A B Q C : List Bool) : next E b A B Q C 6=E 6 := by
  unfold next digitState
  split_ifs <;> simp [tested,copyState,shiftState,splitState,reduced,putPair]

lemma outputs (E : Env Reg) (A B Q C : List Bool) (h2 : E 2=bits C) (h3 : E 3=bits Q) :
    result E A B Q C 2=bits (BinaryDivision.run A B Q C).2 ∧
      result E A B Q C 3=bits (BinaryDivision.run A B Q C).1 := by
  induction A generalizing E Q C with
  | nil => exact ⟨h2,h3⟩
  | cons b A ih => exact ih _ _ _ (next_two E b A B Q C) (next_three E b A B Q C)

open RegisterControl (Runs)

lemma cycle_runs (E F : Env Reg) (b : Bool) (A B Q C : List Bool) (D n : ℕ)
    (h0 : E 0=bits (b::A)) (h1 : E 1=bits B) (h2 : E 2=bits C) (h3 : E 3=bits Q)
    (h4 : E 4=.nil) (h5 : E 5=.nil) (hB : B.length ≤ D) (hC : C.length ≤ D)
    (rest : Runs program (some Point.loop) (next E b A B Q C) F n) :
    Runs program (some Point.loop) E F (100*(D+2)+n) := by
  have hf4 : digitState E b A B C 4=bit (!low b B C) := by
    cases hl : low b B C <;> simp [digitState,hl,putPair,bit]
  have hf3 : digitState E b A B C 3=bits Q := by
    unfold digitState
    split_ifs <;> simp [tested,reduced,copyState,shiftState,splitState,putPair,h3]
  have hpush := cons_exec (digitState E b A B C) 4 3 (by decide) ()
  rw [hf4,hf3] at hpush
  change Exec _ _ (encodeEnv (next E b A B Q C)) _ at hpush
  have hpush' := hpush.mono (show 2*(encode (bit (!low b B C))).length+3 ≤ 9 by
    have := TreeMultiply.bit_length (!low b B C); omega)
  have tail : Runs program (some Point.pushQ) (digitState E b A B C) F (10+n) :=
    Runs.step Point.pushQ _ _ _ _ _ 10 (Effect.call _ _ _ _ 9 hpush') rest
  have ht : Runs program (some Point.test) (tested E b A B C) F (31*D+60+n) := by
    cases hl : low b B C with
    | true =>
      have hx : tested E b A B C 4=.cons .nil .nil := by simp [tested,putPair,hl,bit]
      have hzero := nil_exec (tested E b A B C) 4 ()
      rw [hx] at hzero
      change Exec _ _ (encodeEnv (Function.update (tested E b A B C) 4 .nil)) 5 at hzero
      simp only [digitState,hl,↓reduceIte] at tail
      have hz : Runs program (some Point.zero) (tested E b A B C) F (6+(10+n)) :=
        Runs.step Point.zero _ _ _ _ _ 6 (Effect.call _ _ _ _ 5 hzero) tail
      have htest : Runs program (some Point.test) (tested E b A B C) F (1+(6+(10+n))) :=
        Runs.step Point.test _ _ _ _ _ 1 (Effect.consBranch _ 4 _ _ .nil .nil hx) hz
      exact Runs.weaken _ _ _ _ _ htest (by omega)
    | false =>
      have hx : tested E b A B C 4=.nil := by simp [tested,putPair,hl,bit]
      have hlower : value B ≤ value (b::C) := by
        have hn : ¬ value (b::C)<value B := by simpa only [low,decide_eq_false_iff_not] using hl
        omega
      have hon5 : reduced E b A B C 5=.nil := by simp [reduced,putPair]
      have hon4 : reduced E b A B C 4=.nil := by simp [reduced,tested,putPair,hl,bit]
      have hone := cons_exec (reduced E b A B C) 5 4 (by decide) ()
      rw [hon5,hon4] at hone
      change Exec _ _ (encodeEnv (putPair (reduced E b A B C) 5 4 .nil (bit true))) 5 at hone
      simp only [digitState,hl,Bool.false_eq_true,↓reduceIte] at tail
      have ho : Runs program (some Point.one) (reduced E b A B C) F (6+(10+n)) :=
        Runs.step Point.one _ _ _ _ _ 6 (Effect.call _ _ _ _ 5 hone) tail
      let T := putPair (tested E b A B C) 1 5 (bits B) (bits B)
      have hT2 : T 2=bits (b::C) := by simp [T,tested,copyState,putPair]
      have hT5 : T 5=bits B := by simp [T,putPair]
      have hsub := TreeArithmetic.sub_bits_exec T 2 5 (by decide) (b::C) B hT2 hT5 hlower
      change Exec _ _ (encodeEnv (reduced E b A B C)) _ at hsub
      have hsub' := hsub.mono (show 9*((b::C).length+B.length)+20 ≤ 18*D+29 by
        simp only [List.length_cons]; omega)
      have hs : Runs program (some Point.sub) T F ((18*D+30)+(6+(10+n))) :=
        Runs.step Point.sub _ _ _ _ _ (18*D+30) (Effect.call _ _ _ _ _ hsub') ho
      have hc1 : tested E b A B C 1=bits B := by simp [tested,copyState,putPair]
      have hc5 : tested E b A B C 5=.nil := by simp [tested,putPair]
      have hcopy := copy_exec (tested E b A B C) 1 5 (by decide) ()
      rw [hc1,hc5] at hcopy
      change Exec _ _ (encodeEnv T) (1+3*(encode (bits B)).length+4) at hcopy
      have hcopy' := hcopy.mono (show 1+3*(encode (bits B)).length+4 ≤ 12*D+8 by
        have := bits_length B; omega)
      have hcp : Runs program (some Point.copyD2) (tested E b A B C) F
          ((12*D+9)+((18*D+30)+(6+(10+n)))) :=
        Runs.step Point.copyD2 _ _ _ _ _ (12*D+9) (Effect.call _ _ _ _ _ hcopy') hs
      have htest : Runs program (some Point.test) (tested E b A B C) F
          (1+((12*D+9)+((18*D+30)+(6+(10+n))))) :=
        Runs.step Point.test _ _ _ _ _ 1 (Effect.nilBranch _ 4 _ _ hx) hcp
      exact Runs.weaken _ _ _ _ _ htest (by omega)
  have hc4 : copyState E b A B C 4=bits (b::C) := by simp [copyState,putPair]
  have hc5 : copyState E b A B C 5=bits B := by simp [copyState,putPair]
  have hcmp := TreeArithmetic.less_bits_exec (copyState E b A B C) 4 5 (by decide) (b::C) B hc4 hc5
  change Exec _ _ (encodeEnv (tested E b A B C)) _ at hcmp
  have hcmp' := hcmp.mono (show 3*((b::C).length+B.length)+7 ≤ 6*D+10 by
    simp only [List.length_cons]; omega)
  have hcm : Runs program (some Point.cmp) (copyState E b A B C) F ((6*D+11)+(31*D+60+n)) :=
    Runs.step Point.cmp _ _ _ _ _ (6*D+11) (Effect.call _ _ _ _ _ hcmp') ht
  let U := putPair (shiftState E b A C) 2 4 (bits (b::C)) (bits (b::C))
  have hu1 : U 1=bits B := by simp [U,shiftState,splitState,putPair,h1]
  have hu5 : U 5=.nil := by simp [U,shiftState,splitState,putPair,h5]
  have hcopyD := copy_exec U 1 5 (by decide) ()
  rw [hu1,hu5] at hcopyD
  change Exec _ _ (encodeEnv (copyState E b A B C)) (1+3*(encode (bits B)).length+4) at hcopyD
  have hcopyD' := hcopyD.mono (show 1+3*(encode (bits B)).length+4 ≤ 12*D+8 by
    have := bits_length B; omega)
  have hcd : Runs program (some Point.copyD) U F ((12*D+9)+((6*D+11)+(31*D+60+n))) :=
    Runs.step Point.copyD _ _ _ _ _ (12*D+9) (Effect.call _ _ _ _ _ hcopyD') hcm
  have hs2 : shiftState E b A C 2=bits (b::C) := by simp [shiftState,putPair]
  have hs4 : shiftState E b A C 4=.nil := by simp [shiftState,putPair]
  have hcopyR := copy_exec (shiftState E b A C) 2 4 (by decide) ()
  rw [hs2,hs4] at hcopyR
  change Exec _ _ (encodeEnv U) (1+3*(encode (bits (b::C))).length+4) at hcopyR
  have hcopyR' := hcopyR.mono (show 1+3*(encode (bits (b::C))).length+4 ≤ 12*D+20 by
    have := bits_length (b::C); simp only [List.length_cons] at this; omega)
  have hcr : Runs program (some Point.copyR) (shiftState E b A C) F
      ((12*D+21)+((12*D+9)+((6*D+11)+(31*D+60+n)))) :=
    Runs.step Point.copyR _ _ _ _ _ (12*D+21) (Effect.call _ _ _ _ _ hcopyR') hcd
  have hp4 : splitState E b A 4=bit b := by simp [splitState,putPair]
  have hp2 : splitState E b A 2=bits C := by simp [splitState,putPair,h2]
  have hshift := cons_exec (splitState E b A) 4 2 (by decide) ()
  rw [hp4,hp2] at hshift
  change Exec _ _ (encodeEnv (shiftState E b A C)) _ at hshift
  have hshift' := hshift.mono (show 2*(encode (bit b)).length+3 ≤ 9 by
    have := TreeMultiply.bit_length b; omega)
  have hsh : Runs program (some Point.shift) (splitState E b A) F
      (10+((12*D+21)+((12*D+9)+((6*D+11)+(31*D+60+n))))) :=
    Runs.step Point.shift _ _ _ _ _ 10 (Effect.call _ _ _ _ _ hshift') hcr
  have he0 : E 0=.cons (bit b) (bits A) := h0
  have hsplit := split_exec E 4 0 (by decide) () (bit b) (bits A) he0
  rw [h4] at hsplit
  have hsplit' := hsplit.mono (show (encode Data.nil).length+2*(encode (bit b)).length+4 ≤ 11 by
    have := TreeMultiply.bit_length b; simp only [encode,List.length_cons,List.length_nil]; omega)
  have hsp : Runs program (some Point.split) E F
      (12+(10+((12*D+21)+((12*D+9)+((6*D+11)+(31*D+60+n)))))) :=
    Runs.step Point.split _ _ _ _ _ 12 (Effect.call _ _ _ _ _ hsplit') hsh
  have hloop : Runs program (some Point.loop) E F
      (1+(12+(10+((12*D+21)+((12*D+9)+((6*D+11)+(31*D+60+n))))))) :=
    Runs.step Point.loop _ _ _ _ _ 1 (Effect.consBranch _ 0 _ _ (bit b) (bits A) he0) hsp
  exact Runs.weaken _ _ _ _ _ hloop (by omega)

lemma runs (E : Env Reg) (A B Q C : List Bool) (D : ℕ)
    (h0 : E 0=bits A) (h1 : E 1=bits B) (h2 : E 2=bits C) (h3 : E 3=bits Q)
    (h4 : E 4=.nil) (h5 : E 5=.nil) (hB : B.length ≤ D) (hC : C.length+A.length ≤ D) :
    Runs program (some Point.loop) E (result E A B Q C) (100*(A.length+1)*(D+2)) := by
  induction A generalizing E Q C with
  | nil =>
    have hh : Runs program (some Point.halt) E E 1 :=
      Runs.step Point.halt _ _ _ _ 0 1 (Effect.halt _) (Runs.done _)
    have hl : Runs program (some Point.loop) E E 2 :=
      Runs.step Point.loop _ _ _ _ 1 1 (Effect.nilBranch _ 0 _ _ h0) hh
    exact Runs.weaken _ _ _ _ _ hl (by simp only [List.length_nil]; omega)
  | cons b A ih =>
    have hr := ih (next E b A B Q C) (nextQ b B Q C) (nextR b B C)
      (next_zero E b A B Q C) (next_one E b A B Q C) (next_two E b A B Q C)
      (next_three E b A B Q C) (next_four E b A B Q C) (next_five E b A B Q C)
      (by have := BinaryDivision.nextR_length b B C; simp only [List.length_cons] at hC; omega)
    have hh := cycle_runs E _ b A B Q C D _ h0 h1 h2 h3 h4 h5 hB
      (by simp only [List.length_cons] at hC; omega) hr
    convert hh using 1 <;> simp only [result,List.length_cons]
    ring

def divide : Proc (K Reg) := RegisterControl.compile program

theorem exec (E : Env Reg) (A B Q C : List Bool) (D : ℕ)
    (h0 : E 0=bits A) (h1 : E 1=bits B) (h2 : E 2=bits C) (h3 : E 3=bits Q)
    (h4 : E 4=.nil) (h5 : E 5=.nil) (hB : B.length ≤ D) (hC : C.length+A.length ≤ D) :
    Exec divide (encodeEnv E) (encodeEnv (result E A B Q C)) (100*(A.length+1)*(D+2)) :=
  RegisterControl.compile_exec program _ E _ (runs E A B Q C D h0 h1 h2 h3 h4 h5 hB hC)

end MatchingFPRAS.TreeDivision

end OAI
