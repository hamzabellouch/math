import Mathlib
import OAI.GroupTheory.PeriodicGroups.Machines.UniversalStack

namespace OAI

section
universe u v w
namespace SourceBurnside.UniversalInput
open StackMachine UniversalStack
noncomputable section
variable {K : Type*} [Fintype K] [DecidableEq K]

abbrev Packet (K : Type*) := Option (UniversalStack.Token K)
abbrev width (K : Type*) [Fintype K] := Fintype.card (Packet K)
omit [DecidableEq K] in
lemma width_pos : 0<width K := Fintype.card_pos

def packetBits (p : Packet K) : Fin (width K) → Bool :=
  fun i => decide (i=(Fintype.equivFin (Packet K)) p)
lemma packetBits_injective : Function.Injective (packetBits (K:=K)) := by
  intro a b h
  have he := congrFun h ((Fintype.equivFin (Packet K)) a)
  simp [packetBits] at he
  exact he

def packetDecode (v : Fin (width K) → Bool) : Packet K := Function.invFun packetBits v
lemma packetDecode_bits (p : Packet K) : packetDecode (packetBits p)=p :=
  Function.leftInverse_invFun packetBits_injective p

def packetWord (p : Packet K) : List Bool := List.ofFn (packetBits p)
def binaryCode (P : List (UniversalStack.Token K)) : List Bool :=
  (P.map some++[none]).flatMap packetWord

def header (bits : List Bool) : List Bool := List.replicate bits.length true++false::bits

inductive State (K : Type*) [Fintype K]
  | reverse | reversePut (b : Bool) | header | headerTick | skipPick | skipRead
  | collect (i : Fin (width K)) (v : Fin (width K) → Bool)
  | emit (a : UniversalStack.Token K)
  | universal (s : UniversalStack.State K)
  deriving Fintype

def first : State K := .collect ⟨0,width_pos⟩ (fun _ => false)
def collectNext (i : Fin (width K)) (v : Fin (width K) → Bool) (bit : Bool) : State K :=
  let v' := Function.update v i bit
  if hi : i.val+1<width K then .collect ⟨i.val+1,hi⟩ v' else
    match packetDecode v' with
    | some a => .emit a
    | none => .universal .reset

def machine (src dst : K) : State K → StackMachine.Instr (UniversalStack.Stack K)
    (UniversalStack.Token K) (State K)
  | .reverse => .pop (.reg src) (fun a => match a with
      | none => .header | some (.bit b) => .reversePut b | _ => .universal (.stopped false))
  | .reversePut b => .push (.reg dst) (.bit b) .reverse
  | .header => .pop (.reg dst) (fun a => match a with
      | some (.bit true) => .headerTick | some (.bit false) => .skipPick
      | _ => .universal (.stopped false))
  | .headerTick => .push .pc .tick .header
  | .skipPick => .pop .pc (fun a => if a.isSome then .skipRead else first)
  | .skipRead => .pop (.reg dst) (fun _ => .skipPick)
  | .collect i v => .pop (.reg dst) (fun a => match a with
      | some (.bit b) => collectNext i v b | _ => .universal (.stopped false))
  | .emit a => .push .back a first
  | .universal s => match UniversalStack.interpreter s with
      | .halt => .halt
      | .push k a q => .push k a (.universal q)
      | .pop k f => .pop k (fun a => .universal (f a))

def inputRegs (src dst : K) (u todo : List Bool) : K → List Bool := fun k =>
  if k=src then u else if k=dst then todo.reverse else []
def config (src dst : K) (s : State K) (u todo : List Bool)
    (f b : List (UniversalStack.Token K)) (pc : ℕ) :
    StackMachine.Config (UniversalStack.Stack K) (UniversalStack.Token K) (State K) :=
  ⟨s,(UniversalStack.config .pick (inputRegs src dst u todo) f b pc).store⟩

lemma exec_one (P : State K → StackMachine.Instr (UniversalStack.Stack K)
    (UniversalStack.Token K) (State K)) (C : StackMachine.Config
    (UniversalStack.Stack K) (UniversalStack.Token K) (State K)) :
    exec P C 1=next P C := rfl

variable (src dst : K) (hne : src≠dst)
include hne

lemma reverse_token (u todo : List Bool) (a : Bool) (f b : List (UniversalStack.Token K)) (pc : ℕ) :
    exec (machine src dst) (config src dst .reverse (u++[a]) todo f b pc) 2=
      config src dst .reverse u (a::todo) f b pc := by
  apply config_ext
  · simp [exec,next,machine,config,UniversalStack.config,inputRegs,Ne.symm hne]
  · funext k
    cases k with
    | reg k =>
      by_cases h1 : k=src
      · subst k; simp [exec,next,machine,config,UniversalStack.config,inputRegs,hne]
      · by_cases h2 : k=dst
        · subst k
          simp [exec,next,machine,config,UniversalStack.config,inputRegs,Ne.symm hne,List.reverse_cons]
        · simp [exec,next,machine,config,UniversalStack.config,inputRegs,h1,h2]
    | front => simp [exec,next,machine,config,UniversalStack.config,inputRegs,Ne.symm hne]
    | back => simp [exec,next,machine,config,UniversalStack.config,inputRegs,Ne.symm hne]
    | pc => simp [exec,next,machine,config,UniversalStack.config,inputRegs,Ne.symm hne]

omit hne in
lemma reverse_empty (todo : List Bool) (f b : List (UniversalStack.Token K)) (pc : ℕ) :
    next (machine src dst) (config src dst .reverse [] todo f b pc)=
      config src dst .header [] todo f b pc := by
  apply config_ext
  · simp [next,machine,config,UniversalStack.config,inputRegs]
  · funext k
    cases k with
    | reg k => by_cases h : k=src <;> simp [next,machine,config,UniversalStack.config,inputRegs,h]
    | front => simp [next,machine,config,UniversalStack.config,inputRegs]
    | back => simp [next,machine,config,UniversalStack.config,inputRegs]
    | pc => simp [next,machine,config,UniversalStack.config,inputRegs]

lemma reverse_all (u todo : List Bool) (f b : List (UniversalStack.Token K)) (pc : ℕ) :
    exec (machine src dst) (config src dst .reverse u todo f b pc) (2*u.length+1)=
      config src dst .header [] (u++todo) f b pc := by
  induction u using List.reverseRecOn generalizing todo with
  | nil => simpa [exec] using reverse_empty src dst todo f b pc
  | append_singleton u a ih =>
    rw [List.length_append,List.length_singleton,show 2*(u.length+1)+1=2+(2*u.length+1) by omega,
      exec_from,reverse_token src dst hne,ih]
    simp

lemma header_true (u todo : List Bool) (f b : List (UniversalStack.Token K)) (pc : ℕ) :
    exec (machine src dst) (config src dst .header u (true::todo) f b pc) 2=
      config src dst .header u todo f b (pc+1) := by
  apply config_ext
  · simp [exec,next,machine,config,UniversalStack.config,inputRegs,Ne.symm hne,List.getLast?_reverse]
  · funext k
    cases k with
    | reg k =>
      by_cases h1 : k=src
      · subst k; simp [exec,next,machine,config,UniversalStack.config,inputRegs,hne,Ne.symm hne]
      · by_cases h2 : k=dst
        · subst k; simp [exec,next,machine,config,UniversalStack.config,inputRegs,Ne.symm hne]
        · simp [exec,next,machine,config,UniversalStack.config,inputRegs,h1,h2,Ne.symm hne]
    | front => simp [exec,next,machine,config,UniversalStack.config,inputRegs,Ne.symm hne]
    | back => simp [exec,next,machine,config,UniversalStack.config,inputRegs,Ne.symm hne]
    | pc => simp [exec,next,machine,config,UniversalStack.config,inputRegs,Ne.symm hne,List.replicate_succ']

lemma config_pop_dst (P : State K → StackMachine.Instr (UniversalStack.Stack K)
    (UniversalStack.Token K) (State K)) (s : State K) (g : Option (UniversalStack.Token K) → State K)
    (he : P s=.pop (.reg dst) g) (u todo : List Bool) (a : Bool)
    (f b : List (UniversalStack.Token K)) (pc : ℕ) :
    next P (config src dst s u (a::todo) f b pc)=
      config src dst (g (some (.bit a))) u todo f b pc := by
  apply config_ext
  · simp [next,config,he,UniversalStack.config,inputRegs,Ne.symm hne,List.getLast?_reverse]
  · funext k
    cases k with
    | reg k =>
      by_cases h1 : k=src
      · subst k; simp [next,config,he,UniversalStack.config,inputRegs,hne,Ne.symm hne]
      · by_cases h2 : k=dst
        · subst k; simp [next,config,he,UniversalStack.config,inputRegs,Ne.symm hne]
        · simp [next,config,he,UniversalStack.config,inputRegs,h1,h2,Ne.symm hne]
    | front => simp [next,config,he,UniversalStack.config,inputRegs]
    | back => simp [next,config,he,UniversalStack.config,inputRegs]
    | pc => simp [next,config,he,UniversalStack.config,inputRegs]

lemma header_false (u todo : List Bool) (f b : List (UniversalStack.Token K)) (pc : ℕ) :
    next (machine src dst) (config src dst .header u (false::todo) f b pc)=
      config src dst .skipPick u todo f b pc := by
  exact config_pop_dst src dst hne (machine src dst) .header _ rfl u todo false f b pc

omit hne in
lemma skip_pick_zero (u todo : List Bool) (f b : List (UniversalStack.Token K)) :
    next (machine src dst) (config src dst .skipPick u todo f b 0)=
      config src dst first u todo f b 0 := by
  apply config_ext
  · rfl
  · funext k
    cases k <;> simp [next,machine,config,UniversalStack.config]

omit hne in
lemma skip_pick_succ (u todo : List Bool) (f b : List (UniversalStack.Token K)) (pc : ℕ) :
    next (machine src dst) (config src dst .skipPick u todo f b (pc+1))=
      config src dst .skipRead u todo f b pc := by
  apply config_ext
  · simp [next,machine,config,UniversalStack.config,List.replicate_succ]
  · funext k
    cases k <;> simp [next,machine,config,UniversalStack.config,List.replicate_succ]

lemma skip_read (u todo : List Bool) (a : Bool) (f b : List (UniversalStack.Token K)) (pc : ℕ) :
    next (machine src dst) (config src dst .skipRead u (a::todo) f b pc)=
      config src dst .skipPick u todo f b pc := by
  exact config_pop_dst src dst hne (machine src dst) .skipRead _ rfl u todo a f b pc

lemma header_ones (n : ℕ) (u todo : List Bool) (f b : List (UniversalStack.Token K)) (pc : ℕ) :
    exec (machine src dst) (config src dst .header u (List.replicate n true++todo) f b pc) (2*n)=
      config src dst .header u todo f b (pc+n) := by
  induction n generalizing pc with
  | zero => simp [exec]
  | succ n ih =>
    rw [show 2*(n+1)=2+2*n by omega,List.replicate_succ,List.cons_append,
      exec_from,header_true src dst hne,ih]
    simp [Nat.add_comm,Nat.add_left_comm]

lemma skip_bits (bits u todo : List Bool) (f b : List (UniversalStack.Token K)) :
    exec (machine src dst) (config src dst .skipPick u (bits++todo) f b bits.length)
      (2*bits.length+1)=config src dst first u todo f b 0 := by
  induction bits with
  | nil => simpa [exec] using skip_pick_zero src dst u todo f b
  | cons a bits ih =>
    rw [List.length_cons,List.cons_append,
      show 2*(bits.length+1)+1=1+(1+(2*bits.length+1)) by omega,exec_from]
    rw [exec_one]
    rw [skip_pick_succ src dst,exec_from]
    rw [exec_one]
    rw [skip_read src dst hne,ih]

lemma header_all (bits u todo : List Bool) (f b : List (UniversalStack.Token K)) :
    exec (machine src dst) (config src dst .header u (header bits++todo) f b 0)
      (4*bits.length+2)=config src dst first u todo f b 0 := by
  rw [show 4*bits.length+2=2*bits.length+(1+(2*bits.length+1)) by omega]
  simp only [header,List.append_assoc,List.cons_append]
  rw [exec_from,header_ones src dst hne,Nat.zero_add,exec_from]
  rw [exec_one]
  rw [header_false src dst hne,skip_bits src dst hne]

lemma collect_bit (i : Fin (width K)) (v : Fin (width K) → Bool) (u todo : List Bool) (a : Bool)
    (f b : List (UniversalStack.Token K)) (pc : ℕ) :
    next (machine src dst) (config src dst (.collect i v) u (a::todo) f b pc)=
      config src dst (collectNext i v a) u todo f b pc := by
  exact config_pop_dst src dst hne (machine src dst) (.collect i v) _ rfl u todo a f b pc

def packetState : Packet K → State K
  | none => .universal .reset | some a => .emit a

omit hne in
lemma collect_complete (i : Fin (width K)) (v : Fin (width K) → Bool) (p : Packet K)
    (hv : ∀ j, j.val < i.val → v j=packetBits p j) (hi : ¬i.val+1<width K) :
    collectNext i v (packetBits p i)=packetState p := by
  have hh : Function.update v i (packetBits p i)=packetBits p := by
    funext j
    by_cases he : j=i
    · subst j;simp
    · rw [Function.update_of_ne he]
      exact hv j (by have := j.isLt; have := i.isLt; have hji : j.val ≠ i.val := fun e => he (Fin.ext e);omega)
  rw [collectNext,dite_eq_right hi,hh,packetDecode_bits]; cases p <;> rfl

omit hne [DecidableEq K] in
lemma collect_prefix (i : Fin (width K)) (v : Fin (width K) → Bool) (p : Packet K)
    (hv : ∀ j, j.val < i.val → v j=packetBits p j) :
    ∀j,j.val < i.val+1 → (Function.update v i (packetBits p i)) j=packetBits p j := by
  intro j hj
  by_cases he : j=i
  · subst j;simp
  · rw [Function.update_of_ne he]
    exact hv j (by have hji : j.val ≠ i.val := fun e => he (Fin.ext e);omega)

lemma parse_packet (p : Packet K) (i : Fin (width K)) (v : Fin (width K) → Bool)
    (hv : ∀ j, j.val < i.val → v j=packetBits p j) (u todo : List Bool)
    (f b : List (UniversalStack.Token K)) (pc : ℕ) :
    exec (machine src dst) (config src dst (.collect i v) u ((packetWord p).drop i.val++todo) f b pc)
      (width K-i.val)=config src dst (packetState p) u todo f b pc := by
  generalize hn : width K-i.val=n
  induction n using Nat.strong_induction_on generalizing i v with
  | h n ih =>
    have hilt : i.val<(packetWord p).length := by
      simpa only [packetWord,List.length_ofFn] using i.isLt
    rw [List.drop_eq_getElem_cons hilt,List.cons_append]
    have hiword : (packetWord p)[i.val]=packetBits p i := by
      simp only [packetWord,List.getElem_ofFn]
    rw [hiword]
    by_cases hi : i.val+1<width K
    · rw [show n=1+(width K-(i.val+1)) by omega,exec_from]
      rw [exec_one]
      rw [collect_bit src dst hne]
      simp only [collectNext,hi,dite_eq_left]
      exact ih (width K-(i.val+1)) (by omega) ⟨i.val+1,hi⟩
        (Function.update v i (packetBits p i)) (collect_prefix i v p hv) rfl
    · have hn1 : n=1 := by have := i.isLt;omega
      rw [hn1]
      rw [exec_one]
      rw [collect_bit src dst hne,collect_complete i v p hv hi]
      have he : (packetWord p).drop (i.val+1)=[] := by
        apply List.drop_eq_nil_of_le
        simp only [packetWord,List.length_ofFn]
        omega
      rw [he,List.nil_append]

lemma parse_packet_first (p : Packet K) (u todo : List Bool)
    (f b : List (UniversalStack.Token K)) (pc : ℕ) :
    exec (machine src dst) (config src dst first u (packetWord p++todo) f b pc)
      (width K)=config src dst (packetState p) u todo f b pc := by
  simpa only [first,Nat.sub_zero,List.drop_zero] using
    parse_packet src dst hne p ⟨0,width_pos⟩ (fun _ => false) (by intro j hj;change j.val < 0 at hj;omega) u todo f b pc

omit hne in
lemma emit_token (a : UniversalStack.Token K) (u todo : List Bool)
    (f b : List (UniversalStack.Token K)) (pc : ℕ) :
    next (machine src dst) (config src dst (.emit a) u todo f b pc)=
      config src dst first u todo f (b++[a]) pc := by
  apply config_ext
  · rfl
  · funext k; cases k <;> simp [next,machine,config,UniversalStack.config]

lemma parse_code (P : List (UniversalStack.Token K)) (u todo : List Bool)
    (f b : List (UniversalStack.Token K)) (pc : ℕ) :
    exec (machine src dst) (config src dst first u (binaryCode P++todo) f b pc)
      ((width K+1)*P.length+width K)=
      config src dst (.universal .reset) u todo f (b++P) pc := by
  induction P generalizing b with
  | nil => simpa only [binaryCode,List.map_nil,List.nil_append,List.flatMap_cons,
      List.flatMap_nil,List.append_nil,List.length_nil,Nat.mul_zero,Nat.zero_add,packetState] using
      parse_packet_first src dst hne none u todo f b pc
  | cons a P ih =>
    have hc : binaryCode (a::P)=packetWord (some a)++binaryCode P := by
      simp [binaryCode]
    rw [hc,List.append_assoc,List.length_cons,
      show (width K+1)*(P.length+1)+width K=
        width K+(1+((width K+1)*P.length+width K)) by ring,
      exec_from,parse_packet_first src dst hne]
    change exec (machine src dst) (config src dst (.emit a) u (binaryCode P++todo) f b pc) _=_
    rw [exec_from,exec_one,emit_token src dst,ih]
    simp

def liftConfig (C : StackMachine.Config (UniversalStack.Stack K) (UniversalStack.Token K)
    (UniversalStack.State K)) : StackMachine.Config (UniversalStack.Stack K)
    (UniversalStack.Token K) (State K) := ⟨.universal C.state,C.store⟩

omit hne in
lemma lift_next (C : StackMachine.Config (UniversalStack.Stack K) (UniversalStack.Token K)
    (UniversalStack.State K)) : next (machine src dst) (liftConfig C)=
      liftConfig (next UniversalStack.interpreter C) := by
  cases C with
  | mk s r =>
    cases he : UniversalStack.interpreter s <;> simp [next,machine,liftConfig,he]

omit hne in
lemma lift_exec (C : StackMachine.Config (UniversalStack.Stack K) (UniversalStack.Token K)
    (UniversalStack.State K)) (n : ℕ) : exec (machine src dst) (liftConfig C) n=
      liftConfig (exec UniversalStack.interpreter C n) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [exec,ih,lift_next src dst]

omit hne in
lemma reset_code (P : List (UniversalStack.Token K)) (u todo : List Bool) :
    exec (machine src dst) (config src dst (.universal .reset) u todo [] P 0)
      (2*P.length+1)=config src dst (.universal .pick) u todo P [] 0 := by
  change exec (machine src dst)
    (liftConfig (UniversalStack.config .reset (inputRegs src dst u todo) [] P 0)) _=_
  rw [lift_exec src dst,reset_all,List.append_nil]
  rfl

def loadTime (bits raw : List Bool) (P : List (UniversalStack.Token K)) : ℕ :=
  2*raw.length+1+(4*bits.length+2)+((width K+1)*P.length+width K)+(2*P.length+1)
def rawInput (bits : List Bool) (P : List (UniversalStack.Token K)) (todo : List Bool) :=
  header bits++binaryCode P++todo

theorem load_raw (bits : List Bool) (P : List (UniversalStack.Token K)) (todo : List Bool) :
    exec (machine src dst) (config src dst .reverse (rawInput bits P todo) [] [] [] 0)
      (loadTime bits (rawInput bits P todo) P)=
      config src dst (.universal .pick) [] todo P [] 0 := by
  rw [loadTime,
    exec_from (machine src dst) _ _ (2*P.length+1),
    exec_from (machine src dst) _ _ ((width K+1)*P.length+width K),
    exec_from (machine src dst) _ _ (4*bits.length+2),reverse_all src dst hne]
  simp only [List.append_nil,rawInput,List.append_assoc]
  rw [header_all src dst hne,parse_code src dst hne,List.nil_append,reset_code src dst]

omit hne [DecidableEq K] in
lemma packet_length (p : Packet K) : (packetWord p).length=width K := by
  simp only [packetWord,List.length_ofFn]
omit hne [DecidableEq K] in
lemma binaryCode_length (P : List (UniversalStack.Token K)) :
    (binaryCode P).length=width K*(P.length+1) := by
  induction P with
  | nil => simp [binaryCode,packet_length]
  | cons a P ih =>
    have hc : binaryCode (a::P)=packetWord (some a)++binaryCode P := by simp [binaryCode]
    rw [hc,List.length_append,packet_length,ih,List.length_cons]
    ring
omit hne [DecidableEq K] in
lemma rawInput_length (bits : List Bool) (P : List (UniversalStack.Token K)) (todo : List Bool) :
    (rawInput bits P todo).length=2*bits.length+1+width K*(P.length+1)+todo.length := by
  simp [rawInput,header,binaryCode_length];omega
omit hne [DecidableEq K] in
lemma loadTime_bound (bits : List Bool) (P : List (UniversalStack.Token K)) (todo : List Bool) :
    loadTime bits (rawInput bits P todo) P≤9*(rawInput bits P todo).length+4 := by
  have hw := width_pos (K:=K)
  have hP : P.length≤width K*P.length := by nlinarith
  rw [loadTime,rawInput_length]
  nlinarith

omit hne in
lemma initial_store_length (raw : List Bool) (k : UniversalStack.Stack K) :
    ((config src dst .reverse raw [] [] [] 0).store k).length≤raw.length := by
  cases k with
  | reg k => by_cases hk : k=src <;> simp [config,UniversalStack.config,inputRegs,hk]
  | front => simp [config,UniversalStack.config]
  | back => simp [config,UniversalStack.config]
  | pc => simp [config,UniversalStack.config]

theorem raw_program_halt (P : List (UniversalStack.Instruction K)) (bits todo : List Bool)
    {n : ℕ} {s : K → List Bool} (v w : List (UniversalStack.Instruction K)) (a : Bool)
    (hp : P=v++UniversalStack.Instruction.halt a::w)
    (h : UniversalStack.Run P n 0 (inputRegs src dst [] todo) v.length s) :
    let code := UniversalStack.encodeProgram P
    let raw := rawInput bits code todo
    let budget := loadTime bits raw code+(n+1)*(5*code.length+3)
    ∃ N, N≤budget*(2*(raw.length+budget)+3) ∧
      ∀T, N≤T →
        (OneTape.run (compile (machine src dst))
          (encode (config src dst .reverse raw [] [] [] 0)) T).state =
          .ready (.universal (.stopped a)) := by
  dsimp only
  let code := UniversalStack.encodeProgram P
  let raw := rawInput bits code todo
  let C := config src dst .reverse raw [] [] [] 0
  obtain ⟨t,ht,et⟩ := UniversalStack.simulate_halt P v w a hp h
  have he : exec (machine src dst) C (loadTime bits raw code+t)=
      liftConfig (UniversalStack.config (.stopped a) s
        (.stop::UniversalStack.encodeProgram w) (UniversalStack.encodeProgram v++[.halt a]) 0) := by
    rw [exec_from]
    change exec (machine src dst)
      (exec (machine src dst) (config src dst .reverse (rawInput bits code todo) [] [] [] 0)
        (loadTime bits (rawInput bits code todo) code)) t=_
    rw [load_raw src dst hne]
    change exec (machine src dst)
      (liftConfig (UniversalStack.config .pick (inputRegs src dst [] todo) code [] 0)) t=_
    rw [lift_exec src dst,et]
  refine ⟨clock (machine src dst) C (loadTime bits raw code+t),?_,?_⟩
  · have hb := clock_bound (machine src dst) C raw.length (loadTime bits raw code+t)
      (initial_store_length src dst raw)
    apply hb.trans
    change (loadTime bits raw code+t)*(2*(raw.length+(loadTime bits raw code+t))+3)≤
      (loadTime bits raw code+(n+1)*(5*code.length+3))*
        (2*(raw.length+(loadTime bits raw code+(n+1)*(5*code.length+3)))+3)
    apply Nat.mul_le_mul <;> dsimp only [code] <;> omega
  · intro T hT
    have hh : machine src dst (exec (machine src dst) C (loadTime bits raw code+t)).state=.halt := by
      rw [he];rfl
    have ee := compile_finish (machine src dst) C (loadTime bits raw code+t) T hh hT
    rw [he] at ee
    change (OneTape.run (compile (machine src dst)) (encode C) T).state=_
    rw [ee]
    rfl

end
end SourceBurnside.UniversalInput

namespace SourceBurnside.Structured
noncomputable section
open StackMachine UniversalStack

inductive Program (K : Type*)
  | skip
  | push (k : K) (b : Bool)
  | pop (k : K) (branch : Option Bool → Program K)
  | seq (first second : Program K)
  | loop (k : K) (body : Bool → Program K)

namespace Program
variable {K : Type*}

def Loc : Program K → Type
  | .skip | .push _ _ => Unit
  | .pop _ b => Unit ⊕ ((a : Option Bool) × Loc (b a))
  | .seq p q => Loc p ⊕ Loc q
  | .loop _ b => Unit ⊕ ((a : Bool) × Loc (b a))

instance locFintype (P : Program K) : Fintype P.Loc := by
  induction P with
  | skip => exact inferInstanceAs (Fintype Unit)
  | push k b => exact inferInstanceAs (Fintype Unit)
  | pop k b ih =>
    letI := ih
    exact inferInstanceAs (Fintype (Unit ⊕ ((a : Option Bool) × (b a).Loc)))
  | seq p q ihp ihq =>
    letI := ihp;letI := ihq
    exact inferInstanceAs (Fintype (p.Loc ⊕ q.Loc))
  | loop k b ih =>
    letI := ih
    exact inferInstanceAs (Fintype (Unit ⊕ ((a : Bool) × (b a).Loc)))

def start : (P : Program K) → P.Loc
  | .skip | .push _ _ => ()
  | .pop _ _ | .loop _ _ => .inl ()
  | .seq p _ => .inl p.start

def mapInstr {A Γ Q Q' : Type*} (f : Q → Q') : StackMachine.Instr A Γ Q → StackMachine.Instr A Γ Q'
  | .halt => .halt
  | .push k a q => .push k a (f q)
  | .pop k g => .pop k (fun a => f (g a))

lemma mapInstr_comp {A Γ Q Q' Q'' : Type*} (f : Q → Q') (g : Q' → Q'')
    (i : StackMachine.Instr A Γ Q) : mapInstr g (mapInstr f i)=mapInstr (g ∘ f) i := by
  cases i <;> rfl

def done {A B : Type*} (f : A → B) (last : B) : Option A → B
  | none => last | some a => f a

def operation : (P : Program K) → P.Loc → StackMachine.Instr (Option K) Bool (Option P.Loc)
  | .skip,_ => .pop none (fun _ => none)
  | .push k b,_ => .push (some k) b none
  | .pop k b,.inl _ => .pop (some k) (fun a => some (.inr ⟨a,(b a).start⟩))
  | .pop _ b,.inr ⟨a,s⟩ => mapInstr (Option.map (fun t => .inr ⟨a,t⟩)) ((b a).operation s)
  | .seq p q,.inl s => mapInstr (done (fun t => some (.inl t)) (some (.inr q.start))) (p.operation s)
  | .seq _ q,.inr s => mapInstr (Option.map Sum.inr) (q.operation s)
  | .loop k b,.inl _ => .pop (some k) (fun a => match a with
      | none => none | some a => some (.inr ⟨a,(b a).start⟩))
  | .loop _ b,.inr ⟨a,s⟩ => mapInstr (done (fun t => some (.inr ⟨a,t⟩)) (some (.inl ())))
      ((b a).operation s)

def machine (P : Program K) : Option P.Loc → StackMachine.Instr (Option K) Bool (Option P.Loc)
  | none => .halt | some s => P.operation s

end Program
open Program
variable {K : Type*} [DecidableEq K]

abbrev Store (K : Type*) := K → List Bool

def extendStore (r : Store K) : Option K → List Bool
  | none => [] | some k => r k

inductive Run : Program K → Store K → ℕ → Store K → Prop
  | skip (r) : Run .skip r 1 r
  | push (r) (k) (b) : Run (.push k b) r 1 (Function.update r k (r k++[b]))
  | pop (r : Store K) (k) (b : Option Bool → Program K) (n : ℕ) (s : Store K)
      (h : Run (b (r k).getLast?) (Function.update r k (r k).dropLast) n s) :
      Run (.pop k b) r (1+n) s
  | seq (p q : Program K) (r s t : Store K) (n m : ℕ)
      (hp : Run p r n s) (hq : Run q s m t) : Run (.seq p q) r (n+m) t
  | loop_nil (r : Store K) (k) (b : Bool → Program K) (h : r k=[]) : Run (.loop k b) r 1 r
  | loop_cons (r : Store K) (k) (b : Bool → Program K) (v : List Bool) (a : Bool)
      (s t : Store K) (n m : ℕ) (h : r k=v++[a])
      (hb : Run (b a) (Function.update r k v) n s) (ht : Run (.loop k b) s m t) :
      Run (.loop k b) r (1+(n+m)) t

lemma extendStore_update (r : Store K) (k : K) (v : List Bool) :
    extendStore (Function.update r k v)=Function.update (extendStore r) (some k) v := by
  funext j
  cases j with
  | none => simp [extendStore]
  | some j => by_cases h : j=k <;> simp [extendStore,h]

lemma next_map {Q : Type*} (P : Program K) (M : Q → StackMachine.Instr (Option K) Bool Q)
    (f : Option P.Loc → Q) (s : P.Loc) (r : Store K)
    (h : M (f (some s))=mapInstr f (P.operation s)) :
    next M ⟨f (some s),extendStore r⟩=
      let C := next P.machine ⟨some s,extendStore r⟩
      ⟨f C.state,C.store⟩ := by
  simp only [next,h,machine]
  cases P.operation s <;> rfl

theorem compile_run {P : Program K} {r s : Store K} {n : ℕ} (h : Run P r n s) :
    ∀ {Q : Type*} (M : Q → StackMachine.Instr (Option K) Bool Q) (f : Option P.Loc → Q),
    (∀ l, M (f (some l))=mapInstr f (P.operation l)) →
    exec M ⟨f (some P.start),extendStore r⟩ n=⟨f none,extendStore s⟩ := by
  induction h with
  | skip r =>
    intro Q M f hf
    have he := hf ()
    simp only [operation,mapInstr] at he
    simp [exec,next,he,start,extendStore]
  | push r k b =>
    intro Q M f hf
    have he := hf ()
    simp only [operation,mapInstr] at he
    simp only [exec,next,start,he,extendStore_update]
    rfl
  | pop r k b n s h ih =>
    intro Q M f hf
    rw [exec_from]
    have he := hf (.inl ())
    simp only [operation,mapInstr] at he
    change exec M (next M ⟨f (some (.inl ())),extendStore r⟩) n=_
    simp only [next,he,extendStore]
    let g : Option (b (r k).getLast?).Loc → Q := fun x =>
      f (x.map (fun t => .inr ⟨(r k).getLast?,t⟩))
    have hg : ∀l,M (g (some l))=mapInstr g ((b (r k).getLast?).operation l) := by
      intro l
      change M (f (some (.inr ⟨(r k).getLast?,l⟩)))=_
      have hh := hf (.inr ⟨(r k).getLast?,l⟩)
      change M (f (some (.inr ⟨(r k).getLast?,l⟩)))=
        mapInstr f (mapInstr (Option.map (fun t => .inr ⟨(r k).getLast?,t⟩))
          ((b (r k).getLast?).operation l)) at hh
      exact hh.trans (mapInstr_comp _ _ _)
    have hh := ih M g hg
    dsimp only [g,Option.map] at hh
    rw [extendStore_update] at hh
    exact hh
  | seq p q r s t n m hp hq ihp ihq =>
    intro Q M f hf
    let g : Option p.Loc → Q := fun x =>
      f (done (fun l => some (.inl l)) (some (.inr q.start)) x)
    let j : Option q.Loc → Q := fun x => f (x.map Sum.inr)
    have hg : ∀l,M (g (some l))=mapInstr g (p.operation l) := by
      intro l
      change M (f (some (.inl l)))=_
      have hh := hf (.inl l)
      exact hh.trans (mapInstr_comp _ _ _)
    have hj : ∀l,M (j (some l))=mapInstr j (q.operation l) := by
      intro l
      change M (f (some (.inr l)))=_
      have hh := hf (.inr l)
      exact hh.trans (mapInstr_comp _ _ _)
    rw [exec_from]
    change exec M (exec M ⟨g (some p.start),extendStore r⟩ n) m=_
    rw [ihp M g hg]
    exact ihq M j hj
  | loop_nil r k b hr =>
    intro Q M f hf
    have he := hf (.inl ())
    simp only [operation,mapInstr] at he
    simp only [exec,next,start,he,extendStore,hr,List.getLast?_nil,List.dropLast_nil]
    apply config_ext
    · rfl
    · funext j
      cases j with
      | none => simp [extendStore]
      | some j => by_cases hj : j=k <;> simp [extendStore,hj,hr]
  | loop_cons r k b v a s t n m hr hb ht ihb iht =>
    intro Q M f hf
    let g : Option (b a).Loc → Q := fun x =>
      f (done (fun l => some (.inr ⟨a,l⟩)) (some (.inl ())) x)
    have hg : ∀l,M (g (some l))=mapInstr g ((b a).operation l) := by
      intro l
      change M (f (some (.inr ⟨a,l⟩)))=_
      have hh := hf (.inr ⟨a,l⟩)
      exact hh.trans (mapInstr_comp _ _ _)
    rw [exec_from]
    have he := hf (.inl ())
    simp only [operation,mapInstr] at he
    change exec M (next M ⟨f (some (.inl ())),extendStore r⟩) (n+m)=_
    simp only [next,he,extendStore,hr,List.getLast?_concat,List.dropLast_concat]
    rw [exec_from]
    change exec M (exec M ⟨g (some (b a).start),
      Function.update (extendStore r) (some k) v⟩ n) m=_
    rw [←extendStore_update,ihb M g hg]
    exact iht M f hf

theorem run_machine {P : Program K} {r s : Store K} {n : ℕ} (h : Run P r n s) :
    exec P.machine ⟨some P.start,extendStore r⟩ n=⟨none,extendStore s⟩ := by
  apply compile_run h P.machine id
  intro l
  change P.operation l=mapInstr id (P.operation l)
  cases P.operation l <;> rfl

end
end SourceBurnside.Structured

end

end OAI
