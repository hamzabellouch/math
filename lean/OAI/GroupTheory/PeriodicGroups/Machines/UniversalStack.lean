import Mathlib
import OAI.GroupTheory.PeriodicGroups.Machines.TapePrograms

namespace OAI

section
universe u v w
namespace SourceBurnside.UniversalStack
open StackMachine
noncomputable section
variable {K : Type*} [DecidableEq K]

inductive Instruction (K : Type*)
  | push (k : K) (b : Bool) (go : ℕ)
  | pop (k : K) (zeroTarget one empty : ℕ)
  | halt (result : Bool)
  deriving DecidableEq

inductive Token (K : Type*)
  | push (k : K) (b : Bool)
  | pop (k : K)
  | halt (result : Bool)
  | bit (b : Bool)
  | tick | sep | stop
  deriving DecidableEq, Fintype

inductive Stack (K : Type*)
  | reg (k : K) | front | back | pc
  deriving DecidableEq, Fintype

inductive Target
  | beforeTwo | beforeOne | during | after
  deriving DecidableEq
instance : Fintype Target := Fintype.ofList [.beforeTwo,.beforeOne,.during,.after]
  (by intro x; cases x <;> simp)
inductive Mode
  | skip | opcode | target (t : Target)
  deriving DecidableEq, Fintype
inductive State (K : Type*)
  | reset | restore (a : Token K) | pick
  | read (m : Mode) | remember (m : Mode) (a : Token K)
  | push (k : K) (b : Bool) | pop (k : K) | saveTarget
  | stopped (result : Bool)
  deriving DecidableEq, Fintype

def afterToken : Mode → Token K → State K
  | .skip,.stop => .pick
  | .skip,_ => .read .skip
  | .opcode,.push k b => .push k b
  | .opcode,.pop k => .pop k
  | .opcode,.halt b => .stopped b
  | .opcode,_ => .stopped false
  | .target _,.stop => .reset
  | .target .beforeTwo,.sep => .read (.target .beforeOne)
  | .target .beforeOne,.sep => .read (.target .during)
  | .target .during,.sep | .target .after,.sep => .read (.target .after)
  | .target .during,.tick => .saveTarget
  | .target t,.tick => .read (.target t)
  | .target _,_ => .stopped false

def interpreter : State K → StackMachine.Instr (Stack K) (Token K) (State K)
  | .reset => .pop .back (fun a => match a with | none => .pick | some a => .restore a)
  | .restore a => .push .front a .reset
  | .pick => .pop .pc (fun a => if a.isSome then .read .skip else .read .opcode)
  | .read m => .pop .front (fun a => match a with | none => .stopped false | some a => .remember m a)
  | .remember m a => .push .back a (afterToken m a)
  | .push k b => .push (.reg k) (.bit b) (.read (.target .during))
  | .pop k => .pop (.reg k) (fun a => .read (.target (match a with
      | some (.bit false) => .during | some (.bit true) => .beforeOne | _ => .beforeTwo)))
  | .saveTarget => .push .pc .tick (.read (.target .during))
  | .stopped _ => .halt

def encodeInstruction : Instruction K → List (Token K)
  | .push k b j => [.push k b] ++ List.replicate j .tick ++ [.stop]
  | .pop k z o e => [.pop k] ++ List.replicate z .tick ++ [.sep] ++
      List.replicate o .tick ++ [.sep] ++ List.replicate e .tick ++ [.stop]
  | .halt b => [.halt b,.stop]
def encodeProgram (P : List (Instruction K)) : List (Token K) := P.flatMap encodeInstruction

def config (s : State K) (regs : K → List Bool) (front back : List (Token K)) (pc : ℕ) :
    StackMachine.Config (Stack K) (Token K) (State K) :=
  ⟨s, fun k => match k with
    | .reg k => (regs k).map Token.bit
    | .front => front.reverse | .back => back | .pc => List.replicate pc .tick⟩

omit [DecidableEq K] in
@[simp] lemma config_state (s : State K) (r : K → List Bool) (f b : List (Token K)) (pc : ℕ) :
    (config s r f b pc).state=s := rfl

lemma exec_from {A Γ Q : Type*} [DecidableEq A] (P : Q → StackMachine.Instr A Γ Q)
    (C : StackMachine.Config A Γ Q) (n m : ℕ) :
    exec P C (n+m)=exec P (exec P C n) m := by
  induction m with
  | zero => rfl
  | succ m ih =>
    change next P (exec P C (n+m))=next P (exec P (exec P C n) m)
    exact congrArg (next P) ih
lemma exec_start {A Γ Q : Type*} [DecidableEq A] (P : Q → StackMachine.Instr A Γ Q)
    (C : StackMachine.Config A Γ Q) (n : ℕ) :
    exec P C (n+1)=exec P (next P C) n := by
  rw [Nat.add_comm]
  exact exec_from P C 1 n

lemma config_ext {A Γ Q : Type*} {C D : StackMachine.Config A Γ Q}
    (hs : C.state=D.state) (hk : C.store=D.store) : C=D := by
  cases C; cases D
  cases hs; cases hk
  rfl

lemma read_token (m : Mode) (a : Token K) (r : K → List Bool) (f b : List (Token K)) (pc : ℕ) :
    exec interpreter (config (.read m) r (a::f) b pc) 2 =
      config (afterToken m a) r f (b++[a]) pc := by
  apply config_ext
  · simp [exec,next,interpreter,config,List.getLast?_reverse]
  · funext k
    cases k <;> simp [exec,next,interpreter,config,List.reverse_cons]

lemma save_target (r : K → List Bool) (f b : List (Token K)) (pc : ℕ) :
    next interpreter (config .saveTarget r f b pc)=
      config (.read (.target .during)) r f b (pc+1) := by
  apply config_ext
  · rfl
  · funext k
    cases k <;> simp [next,interpreter,config,List.replicate_succ']

lemma reset_token (a : Token K) (r : K → List Bool) (f b : List (Token K)) (pc : ℕ) :
    exec interpreter (config .reset r f (b++[a]) pc) 2 =
      config .reset r (a::f) b pc := by
  apply config_ext
  · simp [exec,next,interpreter,config]
  · funext k
    cases k <;> simp [exec,next,interpreter,config,List.reverse_cons]

lemma reset_empty (r : K → List Bool) (f : List (Token K)) (pc : ℕ) :
    next interpreter (config .reset r f [] pc)=config .pick r f [] pc := by
  apply config_ext
  · rfl
  · funext k
    cases k <;> simp [next,interpreter,config]

lemma reset_all (r : K → List Bool) (f b : List (Token K)) (pc : ℕ) :
    exec interpreter (config .reset r f b pc) (2*b.length+1)=
      config .pick r (b++f) [] pc := by
  induction b using List.reverseRecOn generalizing f with
  | nil => simpa [exec] using reset_empty r f pc
  | append_singleton b a ih =>
    rw [List.length_append,List.length_singleton,
      show 2*(b.length+1)+1=2+(2*b.length+1) by omega,
      exec_from,reset_token,ih]
    simp

lemma pick_zero (r : K → List Bool) (f b : List (Token K)) :
    next interpreter (config .pick r f b 0)=config (.read .opcode) r f b 0 := by
  apply config_ext
  · rfl
  · funext k
    cases k <;> simp [next,interpreter,config]
lemma pick_succ (r : K → List Bool) (f b : List (Token K)) (pc : ℕ) :
    next interpreter (config .pick r f b (pc+1))=config (.read .skip) r f b pc := by
  apply config_ext
  · simp [next,interpreter,config,List.replicate_succ]
  · funext k
    cases k <;> simp [next,interpreter,config,List.replicate_succ]

omit [DecidableEq K] in
lemma after_skip (a : Token K) (ha : a≠.stop) : afterToken .skip a=.read .skip := by
  cases a <;> simp_all [afterToken]

lemma skip_fragment (v : List (Token K)) (hv : ∀a∈v,a≠.stop)
    (r : K → List Bool) (f b : List (Token K)) (pc : ℕ) :
    exec interpreter (config (.read .skip) r (v++f) b pc) (2*v.length)=
      config (.read .skip) r f (b++v) pc := by
  induction v generalizing b with
  | nil => simp [exec]
  | cons a v ih =>
    rw [List.length_cons,show 2*(v.length+1)=2+2*v.length by omega,
      exec_from,List.cons_append,read_token,after_skip a (hv a (by simp)),
      ih (fun a ha => hv a (by simp [ha]))]
    simp [List.append_assoc]

def codePrefix : Instruction K → List (Token K)
  | .push k b j => [.push k b] ++ List.replicate j .tick
  | .pop k z o e => [.pop k] ++ List.replicate z .tick ++ [.sep] ++
      List.replicate o .tick ++ [.sep] ++ List.replicate e .tick
  | .halt b => [.halt b]
omit [DecidableEq K] in
lemma encode_end (i : Instruction K) : encodeInstruction i=codePrefix i++[.stop] := by
  cases i <;> rfl
omit [DecidableEq K] in
lemma codePrefix_no_stop (i : Instruction K) : ∀a∈codePrefix i,a≠.stop := by
  cases i <;> simp [codePrefix,List.mem_replicate]
  aesop

lemma skip_instruction (i : Instruction K) (r : K → List Bool)
    (f b : List (Token K)) (pc : ℕ) :
    exec interpreter (config (.read .skip) r (encodeInstruction i++f) b pc)
      (2*(encodeInstruction i).length) = config .pick r f (b++encodeInstruction i) pc := by
  rw [encode_end,List.length_append,List.length_singleton,
    show 2*((codePrefix i).length+1)=2*(codePrefix i).length+2 by omega,
    exec_from,List.append_assoc,skip_fragment _ (codePrefix_no_stop i)]
  simpa [afterToken,List.append_assoc] using
    read_token .skip .stop r f (b++codePrefix i) pc

lemma skip_instructions (v : List (Instruction K)) (r : K → List Bool)
    (f b : List (Token K)) (pc : ℕ) :
    exec interpreter (config .pick r (encodeProgram v++f) b (v.length+pc))
      (v.length+2*(encodeProgram v).length)=
      config .pick r f (b++encodeProgram v) pc := by
  induction v generalizing b with
  | nil => simp [encodeProgram,exec]
  | cons a v ih =>
    have ht : (a::v).length+2*(encodeProgram (a::v)).length=
        1+(2*(encodeInstruction a).length+(v.length+2*(encodeProgram v).length)) := by
      simp [encodeProgram]
      omega
    rw [ht,exec_from]
    have he : encodeProgram (a::v)=encodeInstruction a++encodeProgram v := rfl
    rw [he,List.append_assoc,List.length_cons,
      show v.length+1+pc=(v.length+pc)+1 by omega]
    change exec interpreter (next interpreter (config .pick r
      (encodeInstruction a++(encodeProgram v++f)) b ((v.length+pc)+1))) _ = _
    rw [pick_succ,exec_from,skip_instruction,ih]
    simp [List.append_assoc]

lemma fetch (v : List (Instruction K)) (r : K → List Bool)
    (f : List (Token K)) :
    exec interpreter (config .pick r (encodeProgram v++f) [] v.length)
      (v.length+2*(encodeProgram v).length+1)=
      config (.read .opcode) r f (encodeProgram v) 0 := by
  rw [exec_from]
  have hh := skip_instructions v r f [] 0
  simp only [Nat.add_zero,List.nil_append] at hh
  rw [hh]
  exact pick_zero r f (encodeProgram v)

omit [DecidableEq K] in
lemma after_target_tick (t : Target) (ht : t≠.during) :
    afterToken (K:=K) (.target t) .tick=.read (.target t) := by
  cases t <;> simp_all [afterToken]

lemma skip_ticks (t : Target) (ht : t≠.during) (n : ℕ)
    (r : K → List Bool) (f b : List (Token K)) (pc : ℕ) :
    exec interpreter (config (.read (.target t)) r (List.replicate n .tick++f) b pc) (2*n)=
      config (.read (.target t)) r f (b++List.replicate n .tick) pc := by
  induction n generalizing b with
  | zero => simp [exec]
  | succ n ih =>
    rw [show 2*(n+1)=2+2*n by omega,exec_from,List.replicate_succ,List.cons_append,
      read_token,after_target_tick t ht,ih]
    simp [List.append_assoc]

lemma one_target_tick (r : K → List Bool) (f b : List (Token K)) (pc : ℕ) :
    exec interpreter (config (.read (.target .during)) r (.tick::f) b pc) 3=
      config (.read (.target .during)) r f (b++[.tick]) (pc+1) := by
  change exec interpreter _ (2+1)=_
  rw [exec_from,read_token]
  exact save_target r f (b++[.tick]) pc

lemma read_ticks (n : ℕ) (r : K → List Bool) (f b : List (Token K)) (pc : ℕ) :
    exec interpreter (config (.read (.target .during)) r (List.replicate n .tick++f) b pc) (3*n)=
      config (.read (.target .during)) r f (b++List.replicate n .tick) (pc+n) := by
  induction n generalizing b pc with
  | zero => simp [exec]
  | succ n ih =>
    rw [show 3*(n+1)=3+3*n by omega,exec_from,List.replicate_succ,List.cons_append,
      one_target_tick,ih]
    simp [List.append_assoc,Nat.add_comm,Nat.add_left_comm]

lemma push_register (k : K) (a : Bool) (r : K → List Bool)
    (f b : List (Token K)) (pc : ℕ) :
    next interpreter (config (.push k a) r f b pc)=
      config (.read (.target .during)) (Function.update r k (r k++[a])) f b pc := by
  apply config_ext
  · rfl
  · funext j
    cases j with
    | reg j => by_cases h : j=k <;> simp [next,interpreter,config,Function.update_apply,h]
    | front => simp [next,interpreter,config]
    | back => simp [next,interpreter,config]
    | pc => simp [next,interpreter,config]

lemma pop_empty (k : K) (r : K → List Bool) (hr : r k=[])
    (f b : List (Token K)) (pc : ℕ) :
    next interpreter (config (.pop k) r f b pc)=
      config (.read (.target .beforeTwo)) r f b pc := by
  apply config_ext
  · simp [next,interpreter,config,hr]
  · funext j
    cases j with
    | reg j => by_cases h : j=k <;> simp [next,interpreter,config,h,hr]
    | front => simp [next,interpreter,config]
    | back => simp [next,interpreter,config]
    | pc => simp [next,interpreter,config]

lemma pop_snoc (k : K) (a : Bool) (r : K → List Bool) (v : List Bool) (hr : r k=v++[a])
    (f b : List (Token K)) (pc : ℕ) :
    next interpreter (config (.pop k) r f b pc)=
      config (.read (.target (if a then .beforeOne else .during)))
        (Function.update r k v) f b pc := by
  apply config_ext
  · cases a <;> simp [next,interpreter,config,hr]
  · funext j
    cases j with
    | reg j => by_cases h : j=k <;> simp [next,interpreter,config,Function.update_apply,h,hr]
    | front => simp [next,interpreter,config]
    | back => simp [next,interpreter,config]
    | pc => simp [next,interpreter,config]

lemma stop_target (t : Target) (r : K → List Bool) (f b : List (Token K)) (pc : ℕ) :
    exec interpreter (config (.read (.target t)) r (.stop::f) b pc) 2=
      config .reset r f (b++[.stop]) pc := by
  simpa [afterToken] using read_token (.target t) .stop r f b pc

lemma sep_during (r : K → List Bool) (f b : List (Token K)) (pc : ℕ) :
    exec interpreter (config (.read (.target .during)) r (.sep::f) b pc) 2=
      config (.read (.target .after)) r f (b++[.sep]) pc := by
  exact read_token (.target .during) .sep r f b pc
lemma sep_after (r : K → List Bool) (f b : List (Token K)) (pc : ℕ) :
    exec interpreter (config (.read (.target .after)) r (.sep::f) b pc) 2=
      config (.read (.target .after)) r f (b++[.sep]) pc := by
  exact read_token (.target .after) .sep r f b pc
lemma sep_beforeOne (r : K → List Bool) (f b : List (Token K)) (pc : ℕ) :
    exec interpreter (config (.read (.target .beforeOne)) r (.sep::f) b pc) 2=
      config (.read (.target .during)) r f (b++[.sep]) pc := by
  exact read_token (.target .beforeOne) .sep r f b pc
lemma sep_beforeTwo (r : K → List Bool) (f b : List (Token K)) (pc : ℕ) :
    exec interpreter (config (.read (.target .beforeTwo)) r (.sep::f) b pc) 2=
      config (.read (.target .beforeOne)) r f (b++[.sep]) pc := by
  exact read_token (.target .beforeTwo) .sep r f b pc

def popBody (z o e : ℕ) : List (Token K) :=
  List.replicate z .tick ++ [.sep] ++ List.replicate o .tick ++ [.sep] ++
  List.replicate e .tick ++ [.stop]

def selected : Target → ℕ → ℕ → ℕ → ℕ
  | .during,z,_,_ => z | .beforeOne,_,o,_ => o | .beforeTwo,_,_,e => e | .after,_,_,_ => 0

lemma pop_body (t : Target) (z o e : ℕ) (r : K → List Bool) (f b : List (Token K)) (pc : ℕ) :
    exec interpreter (config (.read (.target t)) r (popBody z o e++f) b pc)
      (2*(z+o+e+3)+selected t z o e)=
      config .reset r f (b++popBody z o e) (pc+selected t z o e) := by
  cases t with
  | during =>
    rw [show 2*(z+o+e+3)+selected .during z o e=3*z+(2+(2*o+(2+(2*e+2)))) by simp [selected]; omega]
    simp only [popBody,List.append_assoc,List.cons_append,List.nil_append]
    rw [exec_from,read_ticks,exec_from,sep_during,exec_from,skip_ticks .after (by decide),
      exec_from,sep_after,exec_from,skip_ticks .after (by decide),stop_target]
    simp [selected,List.append_assoc]
  | beforeOne =>
    rw [show 2*(z+o+e+3)+selected .beforeOne z o e=2*z+(2+(3*o+(2+(2*e+2)))) by simp [selected]; omega]
    simp only [popBody,List.append_assoc,List.cons_append,List.nil_append]
    rw [exec_from,skip_ticks .beforeOne (by decide),exec_from,sep_beforeOne,exec_from,read_ticks,
      exec_from,sep_during,exec_from,skip_ticks .after (by decide),stop_target]
    simp [selected,List.append_assoc]
  | beforeTwo =>
    rw [show 2*(z+o+e+3)+selected .beforeTwo z o e=2*z+(2+(2*o+(2+(3*e+2)))) by simp [selected]; omega]
    simp only [popBody,List.append_assoc,List.cons_append,List.nil_append]
    rw [exec_from,skip_ticks .beforeTwo (by decide),exec_from,sep_beforeTwo,exec_from,
      skip_ticks .beforeOne (by decide),exec_from,sep_beforeOne,exec_from,read_ticks,stop_target]
    simp [selected,List.append_assoc]
  | after =>
    rw [show 2*(z+o+e+3)+selected .after z o e=2*z+(2+(2*o+(2+(2*e+2)))) by simp [selected]; omega]
    simp only [popBody,List.append_assoc,List.cons_append,List.nil_append]
    rw [exec_from,skip_ticks .after (by decide),exec_from,sep_after,exec_from,
      skip_ticks .after (by decide),exec_from,sep_after,exec_from,
      skip_ticks .after (by decide),stop_target]
    simp [selected,List.append_assoc]

lemma opcode_push (k : K) (a : Bool) (j : ℕ) (r : K → List Bool)
    (f b : List (Token K)) :
    exec interpreter (config (.read .opcode) r (encodeInstruction (.push k a j)++f) b 0)
      (3*j+5)=
      config .reset (Function.update r k (r k++[a])) f (b++encodeInstruction (.push k a j)) j := by
  rw [show 3*j+5=2+(1+(3*j+2)) by omega]
  simp only [encodeInstruction,List.append_assoc,List.cons_append,List.nil_append]
  rw [exec_from,read_token]
  change exec interpreter (config (.push k a) r _ _ 0) (1+(3*j+2))=_
  rw [exec_from]
  change exec interpreter (next interpreter (config (.push k a) r _ _ 0)) _=_
  rw [push_register,exec_from,read_ticks,stop_target]
  simp [List.append_assoc]

lemma opcode_pop_empty (k : K) (z o e : ℕ) (r : K → List Bool) (hr : r k=[])
    (f b : List (Token K)) :
    exec interpreter (config (.read .opcode) r (encodeInstruction (.pop k z o e)++f) b 0)
      (2*(z+o+e)+e+9)=
      config .reset r f (b++encodeInstruction (.pop k z o e)) e := by
  have he : encodeInstruction (.pop k z o e)=.pop k :: popBody z o e := by
    simp [encodeInstruction,popBody,List.append_assoc]
  rw [he,List.cons_append,show 2*(z+o+e)+e+9=2+(1+(2*(z+o+e+3)+selected .beforeTwo z o e)) by
    simp [selected];omega,exec_from,read_token,exec_from]
  change exec interpreter (next interpreter (config (.pop k) r _ _ 0)) _=_
  rw [pop_empty k r hr,pop_body]
  simp [selected,List.append_assoc]

lemma opcode_pop_snoc (k : K) (a : Bool) (z o e : ℕ) (r : K → List Bool) (v : List Bool)
    (hr : r k=v++[a]) (f b : List (Token K)) :
    exec interpreter (config (.read .opcode) r (encodeInstruction (.pop k z o e)++f) b 0)
      (2*(z+o+e)+(if a then o else z)+9)=
      config .reset (Function.update r k v) f (b++encodeInstruction (.pop k z o e))
        (if a then o else z) := by
  have he : encodeInstruction (.pop k z o e)=.pop k :: popBody z o e := by
    simp [encodeInstruction,popBody,List.append_assoc]
  have ht : 2*(z+o+e)+(if a then o else z)+9=
      2+(1+(2*(z+o+e+3)+selected (if a then .beforeOne else .during) z o e)) := by
    cases a <;> simp [selected] <;> omega
  rw [he,List.cons_append,ht,exec_from,read_token,exec_from]
  change exec interpreter (next interpreter (config (.pop k) r _ _ 0)) _=_
  rw [pop_snoc k a r v hr,pop_body]
  cases a <;> simp [selected,List.append_assoc]

inductive Transfer : Instruction K → (K → List Bool) → (K → List Bool) → ℕ → Prop
  | push (k : K) (a : Bool) (j : ℕ) (r : K → List Bool) :
      Transfer (.push k a j) r (Function.update r k (r k++[a])) j
  | pop_empty (k : K) (z o e : ℕ) (r : K → List Bool) (hr : r k=[]) :
      Transfer (.pop k z o e) r r e
  | pop_snoc (k : K) (a : Bool) (z o e : ℕ) (r : K → List Bool) (v : List Bool)
      (hr : r k=v++[a]) :
      Transfer (.pop k z o e) r (Function.update r k v) (if a then o else z)

lemma opcode_transfer {i : Instruction K} {r r' : K → List Bool} {j : ℕ}
    (h : Transfer i r r' j) (f b : List (Token K)) :
    exec interpreter (config (.read .opcode) r (encodeInstruction i++f) b 0)
      (2*(encodeInstruction i).length+1+j)=
      config .reset r' f (b++encodeInstruction i) j := by
  cases h with
  | push k a j r =>
    convert opcode_push k a j r f b using 1
    simp [encodeInstruction]
    congr 1
    omega
  | pop_empty k z o e r hr =>
    convert opcode_pop_empty k z o j r hr f b using 1
    simp [encodeInstruction]
    congr 1
    omega
  | pop_snoc k a z o e r v hr =>
    convert opcode_pop_snoc k a z o e r v hr f b using 1
    simp [encodeInstruction]
    congr 1
    omega

lemma transfer_jump_le {i : Instruction K} {r r' : K → List Bool} {j : ℕ}
    (h : Transfer i r r' j) : j≤(encodeInstruction i).length := by
  cases h with
  | push k a j r => simp [encodeInstruction];omega
  | pop_empty k z o e r hr => simp [encodeInstruction];omega
  | pop_snoc k a z o e r v hr => cases a <;> simp [encodeInstruction] <;> omega
omit [DecidableEq K] in
lemma instruction_length_pos (i : Instruction K) : 0<(encodeInstruction i).length := by
  cases i <;> simp [encodeInstruction]
omit [DecidableEq K] in
lemma program_length (P : List (Instruction K)) : P.length≤(encodeProgram P).length := by
  induction P with
  | nil => simp [encodeProgram]
  | cons i P ih =>
    change P.length+1≤(encodeInstruction i++encodeProgram P).length
    rw [List.length_append]
    have hi := instruction_length_pos i
    omega

lemma program_step (v w : List (Instruction K)) {i : Instruction K}
    {r r' : K → List Bool} {j : ℕ} (h : Transfer i r r' j) :
    exec interpreter (config .pick r (encodeProgram (v++i::w)) [] v.length)
      (v.length+4*(encodeProgram v).length+4*(encodeInstruction i).length+j+3)=
      config .pick r' (encodeProgram (v++i::w)) [] j := by
  have he : encodeProgram (v++i::w)=encodeProgram v++(encodeInstruction i++encodeProgram w) := by
    simp [encodeProgram]
  rw [he,show v.length+4*(encodeProgram v).length+4*(encodeInstruction i).length+j+3=
      (v.length+2*(encodeProgram v).length+1)+
        ((2*(encodeInstruction i).length+1+j)+
          (2*(encodeProgram v++encodeInstruction i).length+1)) by simp;omega,
    exec_from,fetch,exec_from,opcode_transfer h,reset_all]
  simp [List.append_assoc]

lemma step_clock_le (v w : List (Instruction K)) {i : Instruction K}
    {r r' : K → List Bool} {j : ℕ} (h : Transfer i r r' j) :
    v.length+4*(encodeProgram v).length+4*(encodeInstruction i).length+j+3 ≤
      5*(encodeProgram (v++i::w)).length+3 := by
  have hj := transfer_jump_le h
  have hv := program_length v
  have he : (encodeProgram (v++i::w)).length=
      (encodeProgram v).length+(encodeInstruction i).length+(encodeProgram w).length := by
    simp [encodeProgram,Nat.add_assoc]
  rw [he]
  omega

inductive Run (P : List (Instruction K)) : ℕ → ℕ → (K → List Bool) → ℕ → (K → List Bool) → Prop
  | refl (pc : ℕ) (r : K → List Bool) : Run P 0 pc r pc r
  | step (v w : List (Instruction K)) (i : Instruction K) (hp : P=v++i::w)
      (r r' r'' : K → List Bool) (j last n : ℕ)
      (hi : Transfer i r r' j) (tail : Run P n j r' last r'') :
      Run P (n+1) v.length r last r''

theorem simulate_run (P : List (Instruction K)) {n first last : ℕ} {r s : K → List Bool}
    (h : Run P n first r last s) :
    ∃ N, N≤n*(5*(encodeProgram P).length+3) ∧
      exec interpreter (config .pick r (encodeProgram P) [] first) N =
        config .pick s (encodeProgram P) [] last := by
  induction h with
  | refl pc r => exact ⟨0,by simp,rfl⟩
  | step v w i hp r r' r'' j last n hi tail ih =>
    obtain ⟨N,hN,eN⟩ := ih
    let t := v.length+4*(encodeProgram v).length+4*(encodeInstruction i).length+j+3
    have ht : t≤5*(encodeProgram P).length+3 := by
      rw [hp];exact step_clock_le v w hi
    refine ⟨t+N,?_,?_⟩
    · nlinarith
    · rw [exec_from,hp,program_step v w hi,←hp,eN]

lemma opcode_halt (a : Bool) (r : K → List Bool) (f b : List (Token K)) :
    exec interpreter (config (.read .opcode) r (encodeInstruction (.halt a)++f) b 0) 2=
      config (.stopped a) r (.stop::f) (b++[.halt a]) 0 := by
  exact read_token .opcode (.halt a) r (.stop::f) b 0

lemma program_halt (v w : List (Instruction K)) (a : Bool) (r : K → List Bool) :
    exec interpreter (config .pick r (encodeProgram (v++.halt a::w)) [] v.length)
      (v.length+2*(encodeProgram v).length+3)=
      config (.stopped a) r (.stop::encodeProgram w) (encodeProgram v++[.halt a]) 0 := by
  have he : encodeProgram (v++.halt a::w)=
      encodeProgram v++(encodeInstruction (.halt a)++encodeProgram w) := by
    simp [encodeProgram]
  rw [he,show v.length+2*(encodeProgram v).length+3=
      (v.length+2*(encodeProgram v).length+1)+2 by omega,exec_from,fetch,opcode_halt]

omit [DecidableEq K] in
lemma halt_clock_le (v w : List (Instruction K)) (a : Bool) :
    v.length+2*(encodeProgram v).length+3≤5*(encodeProgram (v++.halt a::w)).length+3 := by
  have hv := program_length v
  have he : (encodeProgram (v++.halt a::w)).length=
      (encodeProgram v).length+2+(encodeProgram w).length := by simp [encodeProgram,encodeInstruction];omega
  rw [he];omega

theorem simulate_halt (P : List (Instruction K)) {n first : ℕ} {r s : K → List Bool}
    (v w : List (Instruction K)) (a : Bool) (hp : P=v++.halt a::w)
    (h : Run P n first r v.length s) :
    ∃ N, N≤(n+1)*(5*(encodeProgram P).length+3) ∧
      exec interpreter (config .pick r (encodeProgram P) [] first) N =
        config (.stopped a) s (.stop::encodeProgram w) (encodeProgram v++[.halt a]) 0 := by
  obtain ⟨N,hN,eN⟩ := simulate_run P h
  refine ⟨N+(v.length+2*(encodeProgram v).length+3),?_,?_⟩
  · have ht := halt_clock_le v w a
    rw [←hp] at ht
    nlinarith
  · rw [exec_from,eN,hp,program_halt]

omit [DecidableEq K] in
lemma config_length_bound (P : List (Instruction K)) (r : K → List Bool) (first m : ℕ)
    (hr : ∀ k, (r k).length ≤ m) (k : Stack K) :
    ((config .pick r (encodeProgram P) [] first).store k).length≤
      m+(encodeProgram P).length+first := by
  cases k with
  | reg k => simp only [config,List.length_map];exact (hr k).trans (by omega)
  | front => simp [config];omega
  | back => simp [config]
  | pc => simp [config]

theorem one_tape_halt (P : List (Instruction K)) {n first : ℕ} {r s : K → List Bool}
    (v w : List (Instruction K)) (a : Bool) (hp : P=v++.halt a::w)
    (h : Run P n first r v.length s) (m : ℕ) (hr : ∀ k, (r k).length ≤ m) :
    ∃ N, N≤((n+1)*(5*(encodeProgram P).length+3))*
        (2*(m+(encodeProgram P).length+first+((n+1)*(5*(encodeProgram P).length+3)))+3) ∧
      ∀T, N≤T →
        OneTape.run (compile interpreter) (encode (config .pick r (encodeProgram P) [] first)) T =
          encode (config (.stopped a) s (.stop::encodeProgram w) (encodeProgram v++[.halt a]) 0) := by
  obtain ⟨t,ht,et⟩ := simulate_halt P v w a hp h
  let C := config .pick r (encodeProgram P) [] first
  refine ⟨clock interpreter C t,?_,?_⟩
  · have hb := clock_bound interpreter C (m+(encodeProgram P).length+first) t
      (config_length_bound P r first m hr)
    apply hb.trans
    apply Nat.mul_le_mul ht
    omega
  · intro T hT
    have halted : interpreter (exec interpreter C t).state=.halt := by
      rw [et];rfl
    simpa only [C,et] using compile_finish interpreter C t T halted hT

section FiniteControl
variable {m : ℕ}

def instructionOf (P : Fin m → StackMachine.Instr K Bool (Fin m)) (result : Fin m → Bool)
    (q : Fin m) : Instruction K := match P q with
  | .halt => .halt (result q)
  | .push k a j => .push k a j.val
  | .pop k f => .pop k (f (some false)).val (f (some true)).val (f none).val

def programOf (P : Fin m → StackMachine.Instr K Bool (Fin m)) (result : Fin m → Bool) :
    List (Instruction K) := List.ofFn (instructionOf P result)

omit [DecidableEq K] in
lemma programOf_split (P : Fin m → StackMachine.Instr K Bool (Fin m)) (result : Fin m → Bool)
    (q : Fin m) :
    programOf P result=(programOf P result).take q.val ++
      instructionOf P result q :: (programOf P result).drop (q.val+1) := by
  have hq : q.val<(programOf P result).length := by simp [programOf]
  conv_lhs => rw [←List.take_append_drop q.val (programOf P result)]
  rw [List.drop_eq_getElem_cons hq]
  simp [programOf]
omit [DecidableEq K] in
lemma programOf_prefix_length (P : Fin m → StackMachine.Instr K Bool (Fin m))
    (result : Fin m → Bool) (q : Fin m) : ((programOf P result).take q.val).length=q.val := by
  simp [List.length_take,programOf]

lemma instructionOf_transfer (P : Fin m → StackMachine.Instr K Bool (Fin m))
    (result : Fin m → Bool) (C : StackMachine.Config K Bool (Fin m))
    (h : P C.state≠.halt) :
    Transfer (instructionOf P result C.state) C.store (next P C).store (next P C).state.val := by
  cases he : P C.state with
  | halt => exact False.elim (h he)
  | push k a j =>
    simpa [instructionOf,next,he] using Transfer.push k a j.val C.store
  | pop k f =>
    have hl : C.store k=[] ∨ ∃v a,C.store k=v++[a] := by
      induction C.store k using List.reverseRecOn with
      | nil => exact Or.inl rfl
      | append_singleton v a _ => exact Or.inr ⟨v,a,rfl⟩
    rcases hl with hl|⟨v,a,hl⟩
    · have hu : Function.update C.store k []=C.store := by
        simpa only [hl] using Function.update_eq_self k C.store
      simpa [instructionOf,next,he,hl,hu] using
        Transfer.pop_empty k (f (some false)).val (f (some true)).val (f none).val C.store hl
    · have hh := Transfer.pop_snoc k a (f (some false)).val (f (some true)).val
        (f none).val C.store v hl
      cases a <;> simpa [instructionOf,next,he,hl] using hh

lemma finite_control_run (P : Fin m → StackMachine.Instr K Bool (Fin m))
    (result : Fin m → Bool) (C : StackMachine.Config K Bool (Fin m)) (n : ℕ)
    (hn : ∀ t, t<n → P (exec P C t).state≠.halt) :
    Run (programOf P result) n C.state.val C.store (exec P C n).state.val (exec P C n).store := by
  induction n generalizing C with
  | zero => exact Run.refl _ _
  | succ n ih =>
    have hC : P C.state≠.halt := hn 0 (by omega)
    have htail : ∀t,t<n → P (exec P (next P C) t).state≠.halt := by
      intro t ht
      rw [←exec_start]
      exact hn (t+1) (by omega)
    have ht := instructionOf_transfer P result C hC
    have hh := Run.step ((programOf P result).take C.state.val)
      ((programOf P result).drop (C.state.val+1)) (instructionOf P result C.state)
      (programOf_split P result C.state) C.store (next P C).store
      (exec P (next P C) n).store (next P C).state.val (exec P (next P C) n).state.val n ht
      (ih (next P C) htail)
    simpa only [programOf_prefix_length,exec_start] using hh

theorem universal_finite_control (P : Fin m → StackMachine.Instr K Bool (Fin m))
    (result : Fin m → Bool) (C : StackMachine.Config K Bool (Fin m)) (n : ℕ)
    (hn : ∀ t, t<n → P (exec P C t).state≠.halt)
    (halted : P (exec P C n).state=.halt) (bound : ℕ) (hbound : ∀ k, (C.store k).length ≤ bound) :
    ∃ N, N≤((n+1)*(5*(encodeProgram (programOf P result)).length+3))*
        (2*(bound+(encodeProgram (programOf P result)).length+C.state.val+
          ((n+1)*(5*(encodeProgram (programOf P result)).length+3)))+3) ∧
      ∀T, N≤T →
        (OneTape.run (compile interpreter)
          (encode (config .pick C.store (encodeProgram (programOf P result)) [] C.state.val)) T).state =
          .ready (.stopped (result (exec P C n).state)) := by
  let pc := (exec P C n).state
  have hid : instructionOf P result pc=.halt (result pc) := by simp [instructionOf,pc,halted]
  have hp := programOf_split P result pc
  rw [hid] at hp
  have hr := finite_control_run P result C n hn
  have hh := one_tape_halt (programOf P result)
    ((programOf P result).take pc.val) ((programOf P result).drop (pc.val+1))
    (result pc) hp (by simpa only [programOf_prefix_length] using hr) bound hbound
  obtain ⟨N,hN,eN⟩ := hh
  refine ⟨N,hN,fun T hT => ?_⟩
  rw [eN T hT]
  rfl
end FiniteControl

end
end SourceBurnside.UniversalStack

end

end OAI
