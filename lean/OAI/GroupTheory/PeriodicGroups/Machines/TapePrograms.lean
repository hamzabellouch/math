import Mathlib

namespace OAI

section
universe u v w

namespace SourceBurnside.OneTape

inductive Move | left | stay | right
  deriving DecidableEq

instance : Fintype Move := ⟨{.left,.stay,.right},by intro a; cases a <;> simp⟩

def Move.shift : Move → ℤ | .left => -1 | .stay => 0 | .right => 1

structure Command (Γ Q : Type*) where
  write : Γ
  next : Q
  move : Move

structure Config (Γ Q : Type*) where
  position : ℤ
  state : Q
  tape : ℤ → Γ

structure Label (Γ Q : Type*) where
  symbol : Γ
  origin : Bool
  head : Option Q
  deriving DecidableEq, Fintype

variable {Γ Q : Type*}

def Config.cell (C : Config Γ Q) (j : ℤ) : Label Γ Q :=
  ⟨C.tape j,decide (j=0),if j=C.position then some C.state else none⟩

def step (δ : Q → Γ → Command Γ Q) (C : Config Γ Q) : Config Γ Q :=
  let cmd := δ C.state (C.tape C.position)
  ⟨C.position+cmd.move.shift,cmd.next,Function.update C.tape C.position cmd.write⟩

def localStep (δ : Q → Γ → Command Γ Q) (left center right : Label Γ Q) : Label Γ Q :=
  let entered := match left.head with
    | some q => let c := δ q left.symbol
                if c.move=Move.right then some c.next else none
    | none => none
  let enteredRight := match right.head with
    | some q => let c := δ q right.symbol
                if c.move=Move.left then some c.next else none
    | none => none
  match center.head with
  | some q => let c := δ q center.symbol
              ⟨c.write,center.origin,if c.move=Move.stay then some c.next else none⟩
  | none => ⟨center.symbol,center.origin,entered.or enteredRight⟩

theorem local_cell (δ : Q → Γ → Command Γ Q) (C : Config Γ Q) (j : ℤ) :
    localStep δ (C.cell (j-1)) (C.cell j) (C.cell (j+1))=(step δ C).cell j := by
  by_cases h0 : j=C.position
  · subst j
    cases he : (δ C.state (C.tape C.position)).move <;>
      simp [localStep,Config.cell,step,Move.shift,he]
  · by_cases hm : j-1=C.position
    · have hp : j+1≠C.position := by omega
      cases he : (δ C.state (C.tape C.position)).move <;>
        simp_all [localStep,Config.cell,step,Move.shift,Function.update] <;> omega
    · by_cases hp : j+1=C.position
      · cases he : (δ C.state (C.tape C.position)).move <;>
          simp_all [localStep,Config.cell,step,Move.shift,Function.update] <;> omega
      · have hml : j≠C.position-1 := by omega
        have hpr : j≠C.position+1 := by omega
        cases he : (δ C.state (C.tape C.position)).move <;>
          simp_all [localStep,Config.cell,step,Move.shift,Function.update]
        omega

def run (δ : Q → Γ → Command Γ Q) (initial : Config Γ Q) : ℕ → Config Γ Q
  | 0 => initial
  | t+1 => step δ (run δ initial t)

lemma step_position_bound (δ : Q → Γ → Command Γ Q) (C : Config Γ Q) :
    C.position-1≤(step δ C).position ∧ (step δ C).position≤C.position+1 := by
  unfold step
  cases he : (δ C.state (C.tape C.position)).move <;> simp [Move.shift,he]
  omega

lemma run_position_bound (δ : Q → Γ → Command Γ Q) (C : Config Γ Q) (t : ℕ) :
    C.position-(t:ℤ)≤(run δ C t).position ∧ (run δ C t).position≤C.position+(t:ℤ) := by
  induction t with
  | zero => simp [run]
  | succ t ih =>
    have hh := step_position_bound δ (run δ C t)
    simp only [run,Nat.cast_add,Nat.cast_one]
    omega

lemma run_tape_untouched (δ : Q → Γ → Command Γ Q) (C : Config Γ Q) (t : ℕ) (j : ℤ)
    (h : ∀ s<t, (run δ C s).position≠j) : (run δ C t).tape j=C.tape j := by
  induction t with
  | zero => rfl
  | succ t ih =>
    change Function.update (run δ C t).tape (run δ C t).position _ j=C.tape j
    rw [Function.update_of_ne (h t (Nat.lt_succ_self t)).symm]
    exact ih (fun s hs => h s (Nat.lt_succ_of_lt hs))

end SourceBurnside.OneTape

namespace SourceBurnside.OneTape
variable {Γ Q : Type*}
lemma run_from (δ : Q → Γ → Command Γ Q) (C : Config Γ Q) (s t : ℕ) :
    run δ C (s+t)=run δ (run δ C s) t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    change step δ (run δ C (s+t)) = step δ (run δ (run δ C s) t)
    exact congrArg (step δ) ih
lemma run_succ_start (δ : Q → Γ → Command Γ Q) (C : Config Γ Q) (t : ℕ) :
    run δ C (t+1)=run δ (step δ C) t := by
  simpa [run,Nat.add_comm] using run_from δ C 1 t
end SourceBurnside.OneTape

namespace SourceBurnside.StackMachine
open OneTape
noncomputable section
local instance tapeProgramsDecidableEq (α : Sort*) : DecidableEq α :=
  Classical.typeDecidableEq α

inductive Instr (K Γ Q : Type*)
  | push (k : K) (a : Γ) (next : Q)
  | pop (k : K) (next : Option Γ → Q)
  | halt
  deriving Fintype

structure Config (K Γ Q : Type*) where
  state : Q
  store : K → List Γ

variable {K Γ Q : Type*} [DecidableEq K]

def next (P : Q → Instr K Γ Q) (C : Config K Γ Q) : Config K Γ Q :=
  match P C.state with
  | .push k a q => ⟨q,Function.update C.store k (C.store k++[a])⟩
  | .pop k q => ⟨q (C.store k).getLast?,Function.update C.store k (C.store k).dropLast⟩
  | .halt => C

def ticks (P : Q → Instr K Γ Q) (C : Config K Γ Q) : ℕ :=
  match P C.state with
  | .push k _ _ | .pop k _ => 2*(C.store k).length+3
  | .halt => 0

structure Symbol (K Γ : Type*) where
  origin : Bool
  track : K → Option Γ
  deriving Fintype

inductive State (K Γ Q : Type*)
  | ready (q : Q)
  | pushFind (k : K) (a : Γ) (q : Q)
  | popFind (k : K) (q : Option Γ → Q)
  | popRead (k : K) (q : Option Γ → Q)
  | back (q : Q)
  deriving Fintype

def compile (P : Q → Instr K Γ Q) : State K Γ Q → Symbol K Γ →
    OneTape.Command (Symbol K Γ) (State K Γ Q)
  | .ready q,s => match P q with
    | .push k a q' => ⟨s,.pushFind k a q',.right⟩
    | .pop k q' => ⟨s,.popFind k q',.right⟩
    | .halt => ⟨s,.ready q,.stay⟩
  | .pushFind k a q,s => if (s.track k).isSome then ⟨s,.pushFind k a q,.right⟩
      else ⟨⟨s.origin,Function.update s.track k (some a)⟩,.back q,.left⟩
  | .popFind k q,s => if (s.track k).isSome then ⟨s,.popFind k q,.right⟩
      else ⟨s,.popRead k q,.left⟩
  | .popRead k q,s => if s.origin then ⟨s,.ready (q none),.stay⟩
      else ⟨⟨s.origin,Function.update s.track k none⟩,.back (q (s.track k)),.left⟩
  | .back q,s => if s.origin then ⟨s,.ready q,.stay⟩ else ⟨s,.back q,.left⟩

def tape (s : K → List Γ) (j : ℤ) : Symbol K Γ :=
  ⟨decide (j=0),fun k => if 0<j then (s k)[j.toNat-1]? else none⟩
def place (s : K → List Γ) (q : State K Γ Q) (j : ℤ) :
    OneTape.Config (Symbol K Γ) (State K Γ Q) := ⟨j,q,tape s⟩
def encode (C : Config K Γ Q) : OneTape.Config (Symbol K Γ) (State K Γ Q) :=
  place C.store (.ready C.state) 0

omit [DecidableEq K] in
@[simp] lemma tape_origin (s : K → List Γ) (j : ℤ) : (tape s j).origin=decide (j=0) := rfl
omit [DecidableEq K] in
@[simp] lemma tape_track_succ (s : K → List Γ) (k : K) (n : ℕ) :
    (tape s ((n:ℤ)+1)).track k=(s k)[n]? := by simp [tape]
omit [DecidableEq K] in
@[simp] lemma tape_track_zero (s : K → List Γ) (k : K) : (tape s 0).track k=none := by
  simp [tape]

lemma step_back_zero (P : Q → Instr K Γ Q) (s : K → List Γ) (q : Q) :
    OneTape.step (compile P) (place s (.back q) 0)=place s (.ready q) 0 := by
  simp [OneTape.step,compile,place,OneTape.Move.shift]

lemma step_back_succ (P : Q → Instr K Γ Q) (s : K → List Γ) (q : Q) (n : ℕ) :
    OneTape.step (compile P) (place s (.back q) ((n:ℤ)+1))=place s (.back q) n := by
  have hn : (n:ℤ)+1≠0 := by omega
  simp [OneTape.step,compile,place,OneTape.Move.shift,hn]

lemma run_back (P : Q → Instr K Γ Q) (s : K → List Γ) (q : Q) (n : ℕ) :
    OneTape.run (compile P) (place s (.back q) n) (n+1)=place s (.ready q) 0 := by
  induction n with
  | zero => exact step_back_zero P s q
  | succ n ih =>
    rw [OneTape.run_succ_start]
    simpa only [Nat.cast_add,Nat.cast_one,step_back_succ] using ih

lemma tape_push (s : K → List Γ) (k : K) (a : Γ) :
    tape (Function.update s k (s k++[a])) =
    Function.update (tape s) ((s k).length+1)
      ⟨false,Function.update (tape s ((s k).length+1)).track k (some a)⟩ := by
  funext j
  by_cases hj : j=(s k).length+1
  · subst j
    have hpos : (0:ℤ)<(s k).length+1 := by omega
    simp only [Function.update_self,tape,show (s k).length+(1:ℤ)≠0 by omega,
      decide_false,ite_eq_left hpos]
    congr 1
    funext i
    by_cases hi : i=k
    · subst i
      simp
    · simp [Function.update_of_ne hi]
  · rw [Function.update_of_ne hj]
    simp only [tape]
    congr 1
    funext i
    by_cases hi : i=k
    · subst i
      simp only [Function.update_self]
      by_cases hpos : 0<j
      · simp only [ite_eq_left hpos]
        by_cases hl : j.toNat-1 < (s k).length
        · exact List.getElem?_append_left hl
        · have hm : (s k).length<j.toNat-1 := by omega
          rw [List.getElem?_eq_none (by simp; omega),List.getElem?_eq_none (by omega)]
      · simp [hpos]
    · simp [Function.update_of_ne hi]

lemma step_push_scan (P : Q → Instr K Γ Q) (s : K → List Γ) (k : K) (a : Γ)
    (q : Q) (n : ℕ) (hn : n<(s k).length) :
    OneTape.step (compile P) (place s (.pushFind k a q) ((n:ℤ)+1))=
      place s (.pushFind k a q) ((n:ℤ)+2) := by
  have ht : ((s k)[n]?).isSome = true := by simpa using hn
  simp [OneTape.step,compile,place,tape_track_succ,ht,OneTape.Move.shift,add_assoc]

lemma step_pop_scan (P : Q → Instr K Γ Q) (s : K → List Γ) (k : K)
    (q : Option Γ → Q) (n : ℕ) (hn : n<(s k).length) :
    OneTape.step (compile P) (place s (.popFind k q) ((n:ℤ)+1))=
      place s (.popFind k q) ((n:ℤ)+2) := by
  have ht : ((s k)[n]?).isSome = true := by simpa using hn
  simp [OneTape.step,compile,place,tape_track_succ,ht,OneTape.Move.shift,add_assoc]

lemma run_push_scan (P : Q → Instr K Γ Q) (s : K → List Γ) (k : K) (a : Γ)
    (q : Q) (n : ℕ) (hn : n≤(s k).length) :
    OneTape.run (compile P) (place s (.pushFind k a q) 1) n=
      place s (.pushFind k a q) ((n:ℤ)+1) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [OneTape.run,ih (by omega),step_push_scan P s k a q n (by omega)]
    congr 1

lemma run_pop_scan (P : Q → Instr K Γ Q) (s : K → List Γ) (k : K)
    (q : Option Γ → Q) (n : ℕ) (hn : n≤(s k).length) :
    OneTape.run (compile P) (place s (.popFind k q) 1) n=
      place s (.popFind k q) ((n:ℤ)+1) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [OneTape.run,ih (by omega),step_pop_scan P s k q n (by omega)]
    congr 1

lemma step_push_write (P : Q → Instr K Γ Q) (s : K → List Γ) (k : K) (a : Γ)
    (q : Q) :
    OneTape.step (compile P) (place s (.pushFind k a q) ((s k).length+1))=
      place (Function.update s k (s k++[a])) (.back q) (s k).length := by
  have hn : (s k).length+(1:ℤ)≠0 := by omega
  simp [OneTape.step,compile,place,tape_track_succ,OneTape.Move.shift,hn,tape_push]

lemma run_push (P : Q → Instr K Γ Q) (C : Config K Γ Q) (k : K) (a : Γ)
    (q : Q) (h : P C.state=.push k a q) :
    OneTape.run (compile P) (encode C) (2*(C.store k).length+3)=
      encode (next P C) := by
  have hs : OneTape.step (compile P) (encode C)=
      place C.store (.pushFind k a q) 1 := by
    simp [OneTape.step,encode,compile,place,h,OneTape.Move.shift]
  rw [show 2*(C.store k).length+3=((C.store k).length+((C.store k).length+2))+1 by omega,
    OneTape.run_succ_start,hs,OneTape.run_from,run_push_scan _ _ _ _ _ _ (by omega),
    OneTape.run_succ_start,step_push_write]
  simpa [next,h,encode] using run_back P (Function.update C.store k (C.store k++[a])) q
    (C.store k).length

lemma tape_pop (s : K → List Γ) (k : K) (hn : 0<(s k).length) :
    tape (Function.update s k (s k).dropLast) =
    Function.update (tape s) (s k).length
      ⟨false,Function.update (tape s (s k).length).track k none⟩ := by
  funext j
  by_cases hj : j=(s k).length
  · subst j
    have hpos : (0:ℤ)<(s k).length := by omega
    simp only [Function.update_self,tape,show (s k).length≠(0:ℤ) by omega,
      decide_false,ite_eq_left hpos,Int.toNat_natCast]
    congr 1
    funext i
    by_cases hi : i=k
    · subst i
      simp
    · simp [Function.update_of_ne hi]
  · rw [Function.update_of_ne hj]
    simp only [tape]
    congr 1
    funext i
    by_cases hi : i=k
    · subst i
      simp only [Function.update_self]
      by_cases hpos : 0<j
      · simp only [ite_eq_left hpos,List.getElem?_dropLast]
        split_ifs with hl
        · rfl
        · symm
          apply List.getElem?_eq_none
          omega
      · simp [hpos]
    · simp [Function.update_of_ne hi]

lemma step_pop_turn (P : Q → Instr K Γ Q) (s : K → List Γ) (k : K)
    (q : Option Γ → Q) :
    OneTape.step (compile P) (place s (.popFind k q) ((s k).length+1))=
      place s (.popRead k q) (s k).length := by
  simp [OneTape.step,compile,place,tape_track_succ,OneTape.Move.shift]

lemma step_pop_read (P : Q → Instr K Γ Q) (s : K → List Γ) (k : K)
    (q : Option Γ → Q) (hn : 0<(s k).length) :
    OneTape.step (compile P) (place s (.popRead k q) (s k).length)=
      place (Function.update s k (s k).dropLast) (.back (q (s k).getLast?))
        ((s k).length-1:ℕ) := by
  have hnil : s k≠[] := by intro he; simp [he] at hn
  have ht : (tape s (s k).length).track k=(s k).getLast? := by
    simp [tape,List.getLast?_eq_getElem?]
  simp [OneTape.step,compile,place,OneTape.Move.shift,hnil,ht,tape_pop s k hn]
  omega

lemma step_pop_empty (P : Q → Instr K Γ Q) (s : K → List Γ) (k : K)
    (q : Option Γ → Q) :
    OneTape.step (compile P) (place s (.popRead k q) 0)=place s (.ready (q none)) 0 := by
  simp [OneTape.step,compile,place,OneTape.Move.shift]

lemma run_pop (P : Q → Instr K Γ Q) (C : Config K Γ Q) (k : K)
    (q : Option Γ → Q) (h : P C.state=.pop k q) :
    OneTape.run (compile P) (encode C) (2*(C.store k).length+3)=
      encode (next P C) := by
  have hs : OneTape.step (compile P) (encode C)=
      place C.store (.popFind k q) 1 := by
    simp [OneTape.step,encode,compile,place,h,OneTape.Move.shift]
  rw [show 2*(C.store k).length+3=((C.store k).length+((C.store k).length+2))+1 by omega,
    OneTape.run_succ_start,hs,OneTape.run_from,run_pop_scan _ _ _ _ _ (by omega),
    OneTape.run_succ_start,step_pop_turn]
  by_cases hn : 0<(C.store k).length
  · rw [OneTape.run_succ_start,step_pop_read _ _ _ _ hn]
    have he := run_back P (Function.update C.store k (C.store k).dropLast)
      (q (C.store k).getLast?) ((C.store k).length-1)
    simpa [next,h,encode,Nat.sub_add_cancel hn] using he
  · have hz : C.store k=[] := List.length_eq_zero_iff.mp (by omega)
    simp only [hz,List.length_nil,Nat.cast_zero,OneTape.run]
    rw [step_pop_empty]
    have hu := Function.update_eq_self k C.store
    rw [hz] at hu
    simp [encode,next,h,hz,hu]

theorem compile_next (P : Q → Instr K Γ Q) (C : Config K Γ Q) :
    OneTape.run (compile P) (encode C) (ticks P C)=encode (next P C) := by
  cases h : P C.state with
  | halt => simp [ticks,next,h,OneTape.run]
  | push k a q => simpa [ticks,h] using run_push P C k a q h
  | pop k q => simpa [ticks,h] using run_pop P C k q h

def exec (P : Q → Instr K Γ Q) (C : Config K Γ Q) : ℕ → Config K Γ Q
  | 0 => C
  | n+1 => next P (exec P C n)
def clock (P : Q → Instr K Γ Q) (C : Config K Γ Q) : ℕ → ℕ
  | 0 => 0
  | n+1 => clock P C n + ticks P (exec P C n)

theorem compile_exec (P : Q → Instr K Γ Q) (C : Config K Γ Q) (n : ℕ) :
    OneTape.run (compile P) (encode C) (clock P C n)=encode (exec P C n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [clock,OneTape.run_from,ih,compile_next]
    rfl

lemma next_length (P : Q → Instr K Γ Q) (C : Config K Γ Q) (k : K) :
    ((next P C).store k).length≤(C.store k).length+1 := by
  cases h : P C.state with
  | halt => simp [next,h]
  | push i a q =>
    by_cases hi : k=i
    · subst k; simp [next,h]
    · simp [next,h,Function.update_of_ne hi]
  | pop i q =>
    by_cases hi : k=i
    · subst k; simp [next,h]; omega
    · simp [next,h,Function.update_of_ne hi]

lemma exec_length (P : Q → Instr K Γ Q) (C : Config K Γ Q) (n : ℕ) (k : K) :
    ((exec P C n).store k).length≤(C.store k).length+n := by
  induction n with
  | zero => simp [exec]
  | succ n ih =>
    have hh := next_length P (exec P C n) k
    simp only [exec]
    omega

omit [DecidableEq K] in
lemma ticks_bound (P : Q → Instr K Γ Q) (C : Config K Γ Q) (m : ℕ)
    (h : ∀ k, (C.store k).length ≤ m) : ticks P C≤2*m+3 := by
  cases he : P C.state with
  | halt => simp [ticks,he]
  | push i a q => simpa [ticks,he] using Nat.add_le_add_right (Nat.mul_le_mul_left 2 (h i)) 3
  | pop i q => simpa [ticks,he] using Nat.add_le_add_right (Nat.mul_le_mul_left 2 (h i)) 3

theorem clock_bound (P : Q → Instr K Γ Q) (C : Config K Γ Q) (m n : ℕ)
    (h : ∀ k, (C.store k).length ≤ m) : clock P C n ≤ n*(2*(m+n)+3) := by
  induction n with
  | zero => simp [clock]
  | succ n ih =>
    have hb : ticks P (exec P C n)≤2*(m+n)+3 :=
      ticks_bound P (exec P C n) (m+n) (fun k =>
        (exec_length P C n k).trans (Nat.add_le_add_right (h k) n))
    simp only [clock]
    nlinarith

lemma halt_step (P : Q → Instr K Γ Q) (C : Config K Γ Q) (h : P C.state=.halt) :
    OneTape.step (compile P) (encode C)=encode C := by
  simp [OneTape.step,compile,encode,place,h,OneTape.Move.shift]

lemma halt_run (P : Q → Instr K Γ Q) (C : Config K Γ Q) (h : P C.state=.halt) (n : ℕ) :
    OneTape.run (compile P) (encode C) n=encode C := by
  induction n with
  | zero => rfl
  | succ n ih => rw [OneTape.run,ih,halt_step P C h]

theorem compile_finish (P : Q → Instr K Γ Q) (C : Config K Γ Q) (n T : ℕ)
    (halted : P (exec P C n).state=.halt) (time : clock P C n≤T) :
    OneTape.run (compile P) (encode C) T=encode (exec P C n) := by
  rw [←Nat.add_sub_of_le time,OneTape.run_from,compile_exec,halt_run _ _ halted]

end
end SourceBurnside.StackMachine

end

end OAI
