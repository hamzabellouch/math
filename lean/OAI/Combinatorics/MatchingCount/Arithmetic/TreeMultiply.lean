import Mathlib
import OAI.Combinatorics.MatchingCount.Machines.RegisterControl
import OAI.Combinatorics.MatchingCount.Tapes.TreeAddBits

namespace OAI

namespace MatchingFPRAS.TreeMultiply
open TreeData TreeMachine RegisterProc Turing
open StackAddition (value value_bits)
open RegisterControl (Instr Runs Effect)

abbrev R := Fin 6
inductive Point where
  | loop | split | test | copy | add | shift | halt
  deriving DecidableEq, Inhabited
instance : Fintype Point := ⟨{.loop,.split,.test,.copy,.add,.shift,.halt},by intro p; cases p <;> simp⟩
def program : Point → RegisterControl.Instr R Point
  | .loop => .branch 0 .halt .split
  | .split => .call (procedure (TreeMachine.Instr.split (Λ:=Unit) 3 0 (by decide) ())) .test
  | .test => .branch 3 .shift .copy
  | .copy => .call (procedure (TreeMachine.Instr.copy (Λ:=Unit) 1 4 (by decide) ())) .add
  | .add => .call (TreeArithmetic.add 2 4 (by decide)) .shift
  | .shift => .call (procedure (TreeMachine.Instr.cons (Λ:=Unit) 4 1 (by decide) ())) .loop
  | .halt => .halt

def prep (E : Env R) (b : Bool) (A : List Bool) : Env R := putPair E 3 0 (bit b) (bits A)
def summed (E : Env R) (b : Bool) (B : List Bool) (c : ℕ) : Env R :=
  if b then putPair (putPair E 1 4 (bits B) (bits B)) 2 4 (nat (c+value B)) .nil else E
def next (E : Env R) (b : Bool) (A B : List Bool) (c : ℕ) : Env R :=
  putPair (summed (prep E b A) b B c) 4 1 .nil (bits (false::B))
def accum (b : Bool) (B : List Bool) (c : ℕ) : ℕ := if b then c+value B else c
def result (E : Env R) : List Bool → List Bool → ℕ → Env R
  | [],_,_ => E
  | b::A,B,c => result (next E b A B c) A (false::B) (accum b B c)

lemma bits_add_length (A B : List Bool) :
    (value A+value B).bits.length≤ max A.length B.length+1 := by
  have hh := BinaryNormalize.normalize_length (StackAddition.addDigits false A B)
  rw [BinaryNormalize.normalize_bits,StackAddition.addDigits_value,Bool.toNat_false,Nat.add_zero] at hh
  exact hh.trans (StackAddition.addDigits_length A B false)
lemma bit_length (b : Bool) : (encode (bit b)).length≤3 := by cases b <;> simp [bit,encode]
lemma next_zero (E : Env R) (b : Bool) (A B : List Bool) (c : ℕ) : next E b A B c 0=bits A := by
  cases b <;> simp [next,summed,prep,putPair]
lemma next_one (E : Env R) (b : Bool) (A B : List Bool) (c : ℕ) : next E b A B c 1=bits (false::B) := by
  simp [next,putPair]
lemma next_two (E : Env R) (b : Bool) (A B : List Bool) (c : ℕ) (hc : E 2=nat c) :
    next E b A B c 2=nat (accum b B c) := by
  cases b <;> simp [next,summed,prep,putPair,accum,hc]
lemma next_three (E : Env R) (b : Bool) (A B : List Bool) (c : ℕ) : next E b A B c 3=bit b := by
  cases b <;> simp [next,summed,prep,putPair]
lemma next_four (E : Env R) (b : Bool) (A B : List Bool) (c : ℕ) : next E b A B c 4=.nil := by
  simp [next,putPair]
lemma next_five (E : Env R) (b : Bool) (A B : List Bool) (c : ℕ) : next E b A B c 5=E 5 := by
  cases b <;> simp [next,summed,prep,putPair]
lemma accum_bound (b : Bool) (A B : List Bool) (c D : ℕ)
    (hB : B.length+(b::A).length≤D) (hc : c.bits.length+(b::A).length≤D) :
    (accum b B c).bits.length+A.length≤D := by
  cases b with
  | false =>
    simp only [accum,Bool.false_eq_true,↓reduceIte]
    simp only [List.length_cons] at hc
    omega
  | true =>
    have hh:=bits_add_length c.bits B
    rw [value_bits] at hh
    simp only [accum,↓reduceIte]
    simp only [List.length_cons] at hB hc
    omega

lemma output (E : Env R) (A B : List Bool) (c : ℕ) (hc : E 2=nat c) :
    result E A B c 2=nat (c+value A*value B) := by
  induction A generalizing E B c with
  | nil => simpa only [result,value,Nat.zero_mul,Nat.add_zero] using hc
  | cons b A ih =>
    rw [result,ih _ _ _ (next_two E b A B c hc)]
    congr 1
    cases b <;> simp only [accum,Bool.false_eq_true,↓reduceIte,value,Bool.toNat_false,
      Bool.toNat_true,Nat.zero_add] <;> ring
lemma frame (E : Env R) (A B : List Bool) (c : ℕ) : result E A B c 5=E 5 := by
  induction A generalizing E B c with
  | nil => rfl
  | cons b A ih => rw [result,ih,next_five]

lemma halt_runs (E : Env R) : Runs program (some Point.halt) E E 1 := by
  exact (Runs.step Point.halt E none E E 0 1 (Effect.halt E) (Runs.done E))

lemma cycle_runs (E F : Env R) (b : Bool) (A B : List Bool) (c D n : ℕ)
    (h0 : E 0=bits (b::A)) (h1 : E 1=bits B) (h2 : E 2=nat c) (h4 : E 4=.nil)
    (hB : B.length≤D) (hc : c.bits.length≤D) (h3 : (encode (E 3)).length≤D+3)
    (rest : Runs program (some Point.loop) (next E b A B c) F n) :
    Runs program (some Point.loop) E F (40*(D+2)+n) := by
  have hshift := cons_exec (summed (prep E b A) b B c) 4 1 (by decide) ()
  have hs4 : summed (prep E b A) b B c 4=.nil := by
    cases b <;> simp [summed,prep,putPair,h4]
  have hs1 : summed (prep E b A) b B c 1=bits B := by
    cases b <;> simp [summed,prep,putPair,h1]
  rw [hs4,hs1] at hshift
  change Exec _ _ (encodeEnv (next E b A B c)) 5 at hshift
  have tail : Runs program (some Point.shift) (summed (prep E b A) b B c) F (6+n) :=
    Runs.step Point.shift _ _ _ _ n 6 (Effect.call _ _ _ _ 5 hshift) rest
  have hh : Runs program (some Point.test) (prep E b A) F (31*D+38+n) := by
    cases b with
    | false =>
      have hx : prep E false A 3=.nil := by simp [prep,putPair,bit]
      have ht : Runs program (some Point.test) (prep E false A) F (1+(6+n)) :=
        Runs.step Point.test _ _ _ _ _ 1 (Effect.nilBranch _ 3 _ _ hx) tail
      exact Runs.weaken _ _ _ _ _ ht (by omega)
    | true =>
      let E' := putPair (prep E true A) 1 4 (bits B) (bits B)
      have hp1 : prep E true A 1=bits B := by simp [prep,putPair,h1]
      have hp4 : prep E true A 4=.nil := by simp [prep,putPair,h4]
      have hcopy := copy_exec (prep E true A) 1 4 (by decide) ()
      rw [hp1,hp4] at hcopy
      change Exec _ _ (encodeEnv E') (1+3*(encode (bits B)).length+4) at hcopy
      have hcopy' := hcopy.mono (show 1+3*(encode (bits B)).length+4≤12*D+8 by
        have := bits_length B; omega)
      have ha2 : E' 2=bits c.bits := by simp [E',prep,putPair,nat,bits,h2]
      have ha4 : E' 4=bits B := by simp [E',putPair]
      have hadd := TreeArithmetic.add_bits_exec E' 2 4 (by decide) c.bits B ha2 ha4
      rw [value_bits] at hadd
      change Exec _ _ (encodeEnv (summed (prep E true A) true B c)) _ at hadd
      have hadd' := hadd.mono (show 9*(c.bits.length+B.length)+20≤18*D+20 by omega)
      have ha : Runs program (some Point.add) E' F ((18*D+21)+(6+n)) :=
        Runs.step Point.add _ _ _ _ _ (18*D+21) (Effect.call _ _ _ _ _ hadd') tail
      have hcp : Runs program (some Point.copy) (prep E true A) F
          ((12*D+9)+((18*D+21)+(6+n))) :=
        Runs.step Point.copy _ _ _ _ _ (12*D+9) (Effect.call _ _ _ _ _ hcopy') ha
      have hx : prep E true A 3=.cons .nil .nil := by simp [prep,putPair,bit]
      have ht : Runs program (some Point.test) (prep E true A) F
          (1+((12*D+9)+((18*D+21)+(6+n)))) :=
        Runs.step Point.test _ _ _ _ _ 1 (Effect.consBranch _ 3 _ _ .nil .nil hx) hcp
      exact Runs.weaken _ _ _ _ _ ht (by omega)
  have he0 : E 0=.cons (bit b) (bits A) := h0
  have hsplit := split_exec E 3 0 (by decide) () (bit b) (bits A) he0
  have hsplit' := hsplit.mono (show (encode (E 3)).length+2*(encode (bit b)).length+4≤D+13 by
    have := bit_length b; omega)
  have hs : Runs program (some Point.split) E F ((D+14)+(31*D+38+n)) :=
    Runs.step Point.split _ _ _ _ _ (D+14) (Effect.call _ _ _ _ _ hsplit') hh
  have hl : Runs program (some Point.loop) E F (1+((D+14)+(31*D+38+n))) :=
    Runs.step Point.loop _ _ _ _ _ 1 (Effect.consBranch _ 0 _ _ (bit b) (bits A) he0) hs
  exact Runs.weaken _ _ _ _ _ hl (by omega)

lemma runs (E : Env R) (A B : List Bool) (c D : ℕ)
    (h0 : E 0=bits A) (h1 : E 1=bits B) (h2 : E 2=nat c) (h4 : E 4=.nil)
    (hB : B.length+A.length≤D) (hc : c.bits.length+A.length≤D)
    (h3 : (encode (E 3)).length≤D+3) :
    Runs program (some Point.loop) E (result E A B c) (40*(A.length+1)*(D+2)) := by
  induction A generalizing E B c with
  | nil =>
    have hl : Runs program (some Point.loop) E E 2 :=
      Runs.step Point.loop E _ E E 1 1 (Effect.nilBranch _ 0 _ _ h0) (halt_runs E)
    exact Runs.weaken _ _ _ _ _ hl (by simp only [List.length_nil]; omega)
  | cons b A ih =>
    have hr := ih (next E b A B c) (false::B) (accum b B c)
      (next_zero E b A B c) (next_one E b A B c) (next_two E b A B c h2)
      (next_four E b A B c) (by simp only [List.length_cons] at hB ⊢; omega)
      (accum_bound b A B c D hB hc) (by rw [next_three]; have := bit_length b; omega)
    have hh := cycle_runs E (result (next E b A B c) A (false::B) (accum b B c))
      b A B c D _ h0 h1 h2 h4 (by simp only [List.length_cons] at hB; omega)
      (by simp only [List.length_cons] at hc; omega) h3 hr
    convert hh using 1 <;> simp only [result,List.length_cons]
    ring

def multiply : Proc (K R) := RegisterControl.compile program

theorem exec (E : Env R) (A B : List Bool) (c D : ℕ)
    (h0 : E 0=bits A) (h1 : E 1=bits B) (h2 : E 2=nat c) (h4 : E 4=.nil)
    (hB : B.length+A.length≤D) (hc : c.bits.length+A.length≤D)
    (h3 : (encode (E 3)).length≤D+3) :
    Exec multiply (encodeEnv E) (encodeEnv (result E A B c)) (40*(A.length+1)*(D+2)) :=
  RegisterControl.compile_exec program _ E _ (runs E A B c D h0 h1 h2 h4 hB hc h3)

end MatchingFPRAS.TreeMultiply

end OAI
