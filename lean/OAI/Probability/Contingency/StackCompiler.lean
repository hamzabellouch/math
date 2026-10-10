import Mathlib
import OAI.Probability.Contingency.DenseWeightBounds

namespace OAI

/-! Stack Compiler. -/

noncomputable section

open scoped BigOperators
namespace Contingency.BitModel.StackCode

inductive Op (labels work : ℕ) where
  | push (i : Fin work) (b : Bool) (next : Fin labels)
  | pop (i : Fin work) (empty zero one : Fin labels)
  | read (empty zero one : Fin labels)
  | coin (zero one : Fin labels)
  | emit (b : Bool) (next : Fin labels)
  | jump (next : Fin labels)
  | halt

structure Program where
  labels : ℕ
  work : ℕ
  start : Fin labels
  code : Fin labels → Op labels work

 

structure Memory (work : ℕ) where
  input : List Bool
  consumed : ℕ
  stack : Fin work → List Bool
  blanks : Fin work → ℕ
  outputRev : List Bool

structure Config (P : Program) where
  state : Option (Fin P.labels)
  memory : Memory P.work

def branch {n : ℕ} (empty zero one : Fin n) : Option Bool → Fin n
  | none => empty
  | some false => zero
  | some true => one

def stackTape (xs : List Bool) (r : ℕ) : Tape :=
  ⟨xs.map some,none,List.replicate r none⟩

def inputTape : List Bool → ℕ → Tape
  | [],p => ⟨List.replicate p none,none,[]⟩
  | b::xs,p => ⟨List.replicate p none,some b,xs.map some⟩

@[simp] theorem tape_keep (t : Tape) : t.move .stay t.head=t := by cases t; rfl

theorem stack_push (xs : List Bool) (r : ℕ) (b : Bool) :
    (stackTape xs r).move .right (some b)=stackTape (b::xs) (r-1) := by
  cases r <;> simp [stackTape,Tape.move,List.replicate_succ]

theorem stack_pop_empty (r : ℕ) :
    ((stackTape [] r).move .left none).move .stay none=stackTape [] (r+1) := by
  simp [stackTape,Tape.move,List.replicate_succ]

theorem stack_pop_cons (b : Bool) (xs : List Bool) (r : ℕ) :
    ((stackTape (b::xs) r).move .left none).move .stay none=stackTape xs (r+1) := by
  simp [stackTape,Tape.move,List.replicate_succ]

theorem stack_pop_head (xs : List Bool) (r : ℕ) :
    ((stackTape xs r).move .left none).head=xs.head? := by cases xs <;> rfl

theorem input_read (xs : List Bool) (p : ℕ) :
    (inputTape xs p).move .right none=inputTape xs.tail (p+1) := by
  cases xs with
  | nil => simp [inputTape,Tape.move,List.replicate_succ]
  | cons b xs => cases xs <;> simp [inputTape,Tape.move,List.replicate_succ]

@[simp] theorem inputTape_head (xs : List Bool) (p : ℕ) :
    (inputTape xs p).head=xs.head? := by cases xs <;> rfl

def Memory.tapes {w : ℕ} (m : Memory w) : Fin (w+1) → Tape :=
  Fin.lastCases (inputTape m.input m.consumed) (fun i => stackTape (m.stack i) (m.blanks i))

@[simp] theorem tapes_work {w : ℕ} (m : Memory w) (i : Fin w) :
    m.tapes i.castSucc=stackTape (m.stack i) (m.blanks i) := by simp [Memory.tapes]

@[simp] theorem tapes_input {w : ℕ} (m : Memory w) :
    m.tapes (Fin.last w)=inputTape m.input m.consumed := by simp [Memory.tapes]

def Memory.push {w : ℕ} (m : Memory w) (i : Fin w) (b : Bool) : Memory w :=
  {m with stack := Function.update m.stack i (b::m.stack i)
          blanks := Function.update m.blanks i (m.blanks i-1)}

def Memory.pop {w : ℕ} (m : Memory w) (i : Fin w) : Memory w :=
  {m with stack := Function.update m.stack i (m.stack i).tail
          blanks := Function.update m.blanks i (m.blanks i+1)}

def Memory.read {w : ℕ} (m : Memory w) : Memory w :=
  {m with input := m.input.tail,consumed := m.consumed+1}

def effect {l w : ℕ} (op : Op l w) (coin : Bool) (m : Memory w) : Option (Fin l) × Memory w :=
  match op with
  | .push i b next => (some next,m.push i b)
  | .pop i e z o => (some (branch e z o (m.stack i).head?),m.pop i)
  | .read e z o => (some (branch e z o m.input.head?),m.read)
  | .coin z o => (some (if coin then o else z),m)
  | .emit b next => (some next,{m with outputRev := b::m.outputRev})
  | .jump next => (some next,m)
  | .halt => (none,m)

def step (P : Program) (coin : Bool) (c : Config P) : Config P :=
  match c.state with
  | none => c
  | some pc => let e := effect (P.code pc) coin c.memory; ⟨e.1,e.2⟩

def first {l : ℕ} (pc : Fin l) : Fin (l*2) := finProdFinEquiv (pc,0)
def second {l : ℕ} (pc : Fin l) : Fin (l*2) := finProdFinEquiv (pc,1)

def preserved {l t : ℕ} (next : Option (Fin l)) (heads : Fin t → Option Bool)
    (emit : Option Bool := none) : Instruction l t :=
  ⟨next,heads,fun _ => .stay,emit⟩

def active {l t : ℕ} (next : Option (Fin l)) (heads : Fin t → Option Bool)
    (i : Fin t) (write : Option Bool) (move : Move) : Instruction l t :=
  ⟨next,Function.update heads i write,Function.update (fun _ => .stay) i move,none⟩

def prepare (P : Program) (pc : Fin P.labels) (heads : Fin (P.work+1) → Option Bool) :
    Instruction (P.labels*2) (P.work+1) :=
  match P.code pc with
  | .pop i _ _ _ => active (some (second pc)) heads i.castSucc (heads i.castSucc) .left
  | _ => preserved (some (second pc)) heads

def execute (P : Program) (pc : Fin P.labels) (coin : Bool)
    (heads : Fin (P.work+1) → Option Bool) : Instruction (P.labels*2) (P.work+1) :=
  match P.code pc with
  | .push i b next => active (some (first next)) heads i.castSucc (some b) .right
  | .pop i e z o => active (some (first (branch e z o (heads i.castSucc)))) heads i.castSucc none .stay
  | .read e z o => active (some (first (branch e z o (heads (Fin.last P.work))))) heads (Fin.last P.work) none .right
  | .coin z o => preserved (some (first (if coin then o else z))) heads
  | .emit b next => preserved (some (first next)) heads (some b)
  | .jump next => preserved (some (first next)) heads
  | .halt => preserved none heads

 

def compile (P : Program) : Machine where
  states := P.labels*2
  tapes := P.work+1
  start := first P.start
  inputTape := Fin.last P.work
  transition s coin heads :=
    let cp := finProdFinEquiv.symm s
    if cp.2=0 then prepare P cp.1 heads else execute P cp.1 coin heads

def encode (P : Program) (c : Config P) : BitModel.Config (compile P) :=
  ⟨c.state.map first,c.memory.tapes,c.memory.outputRev⟩

@[simp] theorem compile_first (P : Program) (pc : Fin P.labels) (coin : Bool) (heads) :
    (compile P).transition (first pc) coin heads=prepare P pc heads := by
  simp [compile,first]

@[simp] theorem compile_second (P : Program) (pc : Fin P.labels) (coin : Bool) (heads) :
    (compile P).transition (second pc) coin heads=execute P pc coin heads := by
  simp [compile,second]

theorem move_preserved {t : ℕ} (ts : Fin t → Tape) :
    (fun i => (ts i).move .stay (ts i).head)=ts := by funext i; exact tape_keep _

theorem move_active {t : ℕ} (ts : Fin t → Tape) (i : Fin t) (a : Option Bool) (d : Move) :
    (fun j => (ts j).move (Function.update (fun _ => Move.stay) i d j)
      (Function.update (fun k => (ts k).head) i a j)) =
      Function.update ts i ((ts i).move d a) := by
  funext j
  by_cases h : j=i <;> simp [h]

theorem tapes_push {w : ℕ} (m : Memory w) (i : Fin w) (b : Bool) :
    (m.push i b).tapes=Function.update m.tapes i.castSucc
      ((m.tapes i.castSucc).move .right (some b)) := by
  funext j
  refine Fin.lastCases ?_ (fun k => ?_) j
  · simp [Memory.tapes,Memory.push,Function.update_apply, ne_of_gt (Fin.castSucc_lt_last i)]
  · by_cases h : k=i
    · subst k; simp [Memory.push,stack_push]
    · simp [Memory.push,h]

theorem tapes_pop {w : ℕ} (m : Memory w) (i : Fin w) :
    (m.pop i).tapes=Function.update m.tapes i.castSucc
      (((m.tapes i.castSucc).move .left none).move .stay none) := by
  funext j
  refine Fin.lastCases ?_ (fun k => ?_) j
  · simp [Memory.tapes,Memory.pop,Function.update_apply, ne_of_gt (Fin.castSucc_lt_last i)]
  · by_cases h : k=i
    · subst k
      simp only [tapes_work,Memory.pop,Function.update_self]
      cases m.stack i <;> simp [stack_pop_empty,stack_pop_cons]
    · simp [Memory.pop,h]

theorem tapes_read {w : ℕ} (m : Memory w) :
    m.read.tapes=Function.update m.tapes (Fin.last w)
      ((m.tapes (Fin.last w)).move .right none) := by
  funext j
  refine Fin.lastCases ?_ (fun k => ?_) j
  · simp [Memory.read,input_read]
  · simp [Memory.read]

 
theorem two_steps (P : Program) (noise coin : Bool) (c : Config P) :
    (compile P).step coin ((compile P).step noise (encode P c)) =
      encode P (step P coin c) := by
  rcases c with ⟨state,m⟩
  cases state with
  | none => rfl
  | some pc =>
    change (compile P).step coin ((compile P).step noise
      ⟨some (first pc),m.tapes,m.outputRev⟩) =
      encode P ⟨(effect (P.code pc) coin m).1,(effect (P.code pc) coin m).2⟩
    cases h : P.code pc <;>
      simp [Machine.step,compile_first,prepare,h,active,preserved,
        compile_second,execute,encode,effect,Option.map] <;> try rfl
    case push i b next =>
      congr 1
      exact (move_active m.tapes i.castSucc (some b) .right).trans (tapes_push m i b).symm
    case read e z o =>
      congr 1
      exact (move_active m.tapes (Fin.last P.work) none .right).trans (tapes_read m).symm
    case pop i e z o =>
      congr 1
      · dsimp only [compile] at *
        simp only [Function.update_self]
        change some (first (branch e z o ((stackTape (m.stack i) (m.blanks i)).move .left none).head))=_
        rw [stack_pop_head]
      · dsimp only [compile] at *
        funext j
        refine Fin.lastCases ?_ (fun k => ?_) j
        · have hi : Fin.last P.work ≠ i.castSucc := ne_of_gt (Fin.castSucc_lt_last i)
          simp [Function.update_apply,hi,Memory.pop]
          simpa using tape_keep (inputTape m.input m.consumed)
        · by_cases hk : k=i
          · subst k
            simp only [Function.update_self,tapes_work,Memory.pop]
            change ((stackTape (m.stack i) (m.blanks i)).move .left none).move .stay none=_
            cases hxs : m.stack i <;>
              simp [stack_pop_empty,stack_pop_cons]
          · simp [Function.update_apply,hk,Memory.pop]

end Contingency.BitModel.StackCode

 

 

 

open scoped BigOperators
namespace Contingency.BitModel.StackCode

def initial (P : Program) (xs : List Bool) : Config P :=
  ⟨some P.start,⟨xs,0,fun _ => [],fun _ => 0,[]⟩⟩

def run (P : Program) (xs : List Bool) {t : ℕ} (coins : Fin t → Bool) : Config P :=
  (List.ofFn coins).foldl (fun c b => step P b c) (initial P xs)

theorem initial_eq (P : Program) (xs : List Bool) :
    encode P (initial P xs)=(compile P).initial xs := by
  unfold encode initial Machine.initial compile
  congr 1
  funext j
  refine Fin.lastCases ?_ (fun i => ?_) j
  · simp only [tapes_input,ite_true]
    cases xs <;> rfl
  · simp only [tapes_work,Fin.castSucc_ne_last,ite_false]
    rfl

theorem fold_pairs (P : Program) (ps : List (Bool×Bool)) (c : Config P) :
    (ps.flatMap fun p => [p.1,p.2]).foldl (fun c b => (compile P).step b c) (encode P c) =
      encode P (ps.foldl (fun c p => step P p.2 c) c) := by
  induction ps generalizing c with
  | nil => rfl
  | cons p ps ih =>
    simp only [List.flatMap_cons,List.foldl_append,List.foldl_cons,List.foldl_nil]
    rw [two_steps,ih]

theorem coins_as_pairs {t : ℕ} (coins : Fin (t*2) → Bool) :
    List.ofFn coins=(List.ofFn fun i : Fin t => (coins (first i),coins (second i))).flatMap
      (fun p => [p.1,p.2]) := by
  rw [List.ofFn_mul,List.flatMap_def,List.map_ofFn]
  congr 1
  apply congrArg List.ofFn
  funext i
  simp [List.ofFn_succ,first,second,finProdFinEquiv,Nat.mul_comm,Nat.add_comm]

 
theorem run_eq (P : Program) (xs : List Bool) {t : ℕ} (coins : Fin (t*2) → Bool) :
    (compile P).run xs coins=encode P (run P xs (fun i => coins (second i))) := by
  unfold Machine.run
  rw [← initial_eq,coins_as_pairs,fold_pairs]
  unfold run
  congr 1
  have hh := List.foldl_map (f:=Prod.snd) (g:=fun c b => step P b c)
    (l:=List.ofFn fun i : Fin t => (coins (first i),coins (second i))) (init:=initial P xs)
  simpa only [List.map_ofFn,Function.comp_def] using hh.symm

def coinPairs (t : ℕ) : (Fin (t*2) → Bool) ≃ (Fin t → Bool)×(Fin t → Bool) where
  toFun f := (fun i => f (first i),fun i => f (second i))
  invFun p j := let q := finProdFinEquiv.symm j
    if q.2=0 then p.1 q.1 else p.2 q.1
  left_inv f := by
    funext j
    obtain ⟨⟨i,k⟩,rfl⟩ := finProdFinEquiv.surjective j
    fin_cases k <;> simp [first,second]
  right_inv p := by
    rcases p with ⟨a,b⟩
    apply Prod.ext <;> funext i <;> simp [first,second]

 
theorem count_second (t : ℕ) (p : (Fin t → Bool) → Prop) [DecidablePred p] :
    (Finset.univ.filter fun c : Fin (t*2) → Bool => p (fun i => c (second i))).card =
      2^t*(Finset.univ.filter p).card := by
  classical
  simp only [Finset.card_filter]
  change (∑ c,if p ((coinPairs t c).2) then 1 else 0)=_
  rw [(coinPairs t).sum_comp (fun ab => if p ab.2 then (1:ℕ) else 0),Fintype.sum_prod_type]
  simp

noncomputable def mass (P : Program) (xs out : List Bool) (t : ℕ) : ℝ :=
  ((Finset.univ.filter fun coins : Fin t → Bool => (run P xs coins).state=none ∧
    (run P xs coins).memory.outputRev.reverse=out).card:ℝ)/2^t

noncomputable def tail (P : Program) (xs : List Bool) (t : ℕ) : ℝ :=
  ((Finset.univ.filter fun coins : Fin t → Bool => (run P xs coins).state≠none).card:ℝ)/2^t

@[simp] theorem encode_halt (P : Program) (c : Config P) :
    (encode P c).state=none ↔ c.state=none := by cases h : c.state <;> simp [encode,h,Option.map]

@[simp] theorem encode_output (P : Program) (c : Config P) :
    (encode P c).outputRev=c.memory.outputRev := rfl

theorem mass_compile (P : Program) (xs out : List Bool) (t : ℕ) :
    (compile P).mass xs out (t*2)=mass P xs out t := by
  classical
  unfold Machine.mass
  simp only [run_eq,encode_halt,encode_output]
  rw [count_second t (fun c => (run P xs c).state=none ∧
    (run P xs c).memory.outputRev.reverse=out)]
  unfold mass
  push_cast
  rw [pow_mul,pow_two]
  field_simp

theorem tail_compile (P : Program) (xs : List Bool) (t : ℕ) :
    (compile P).tail xs (t*2)=tail P xs t := by
  classical
  unfold Machine.tail
  simp only [run_eq,ne_eq,encode_halt]
  rw [count_second t (fun c => (run P xs c).state≠none)]
  unfold tail
  push_cast
  rw [pow_mul,pow_two]
  field_simp

end Contingency.BitModel.StackCode

 

 

 

namespace Contingency.BitModel.StackCode.BinaryTrial
noncomputable section

inductive Cmp | lt | eq | gt
  deriving DecidableEq

instance : Fintype Cmp where
  elems := {.lt,.eq,.gt}
  complete := by intro s; cases s <;> simp

def advance (s : Cmp) (bound coin : Bool) : Cmp :=
  match s with
  | .lt => .lt
  | .gt => .gt
  | .eq => if coin=bound then .eq else if coin then .gt else .lt

def accept : Cmp → Bool
  | .lt | .eq => true
  | .gt => false

inductive Q
  | start (s : Cmp)
  | save (s : Cmp) (bound : Bool)
  | choose (s : Cmp) (bound : Bool)
  | place (s : Cmp) (bound coin : Bool)
  | finish (s : Cmp)
  | halt
  deriving DecidableEq, Fintype

def label (q : Q) : Fin (Fintype.card Q) := Fintype.equivFin Q q

def code : Q → Op (Fintype.card Q) 4
  | .start s => .pop 0 (label (.finish s)) (label (.save s false)) (label (.save s true))
  | .save s v => .push 2 v (label (.choose s v))
  | .choose s v => .coin (label (.place s v false)) (label (.place s v true))
  | .place s v b => .push 1 b (label (.start (advance s v b)))
  | .finish s => .push 3 (accept s) (label .halt)
  | .halt => .halt

def program : Program :=
  ⟨Fintype.card Q,4,label (.start .eq),fun pc => code ((Fintype.equivFin Q).symm pc)⟩

def config (q : Q) (m : Memory 4) : Config program := ⟨some (label q),m⟩

@[simp] theorem program_code (q : Q) : program.code (label q)=code q := by
  simp [program,label]

 
theorem one_step (q : Q) (m : Memory 4) (coin : Bool) :
    step program coin (config q m)=
      ⟨(effect (code q) coin m).1,(effect (code q) coin m).2⟩ := by
  simp [step,config,program,label]

def digitMemory (m : Memory 4) (v b : Bool) : Memory 4 := ((m.pop 0).push 2 v).push 1 b

@[simp] theorem digit_stack0 (m : Memory 4) (v b : Bool) :
    (digitMemory m v b).stack 0=(m.stack 0).tail := by simp [digitMemory,Memory.pop,Memory.push]
@[simp] theorem digit_stack1 (m : Memory 4) (v b : Bool) :
    (digitMemory m v b).stack 1=b::m.stack 1 := by simp [digitMemory,Memory.pop,Memory.push]
@[simp] theorem digit_stack2 (m : Memory 4) (v b : Bool) :
    (digitMemory m v b).stack 2=v::m.stack 2 := by simp [digitMemory,Memory.pop,Memory.push]
@[simp] theorem digit_stack3 (m : Memory 4) (v b : Bool) :
    (digitMemory m v b).stack 3=m.stack 3 := by simp [digitMemory,Memory.pop,Memory.push]

theorem four_steps (s : Cmp) (m : Memory 4) (v b n₀ n₁ n₃ : Bool) (rest : List Bool)
    (hm : m.stack 0=v::rest) :
    [n₀,n₁,b,n₃].foldl (fun c z => step program z c) (config (.start s) m)=
      config (.start (advance s v b)) (digitMemory m v b) := by
  cases v <;> cases b <;>
    simp [List.foldl_cons,List.foldl_nil,code,effect,branch,hm,config,digitMemory,
      step,program,label]

structure Digit where
  bound : Bool
  coin : Bool
  noise₀ : Bool
  noise₁ : Bool
  noise₃ : Bool

def bits (d : Digit) : List Bool := [d.noise₀,d.noise₁,d.coin,d.noise₃]

def wordMemory (ds : List Digit) (m : Memory 4) : Memory 4 :=
  ds.foldl (fun m d => digitMemory m d.bound d.coin) m

def wordCmp (ds : List Digit) (s : Cmp) : Cmp :=
  ds.foldl (fun s d => advance s d.bound d.coin) s

theorem pass (ds : List Digit) (s : Cmp) (m : Memory 4)
    (hm : m.stack 0=ds.map Digit.bound) :
    (ds.flatMap bits).foldl (fun c b => step program b c) (config (.start s) m)=
      config (.start (wordCmp ds s)) (wordMemory ds m) := by
  induction ds generalizing s m with
  | nil => rfl
  | cons d ds ih =>
    simp only [List.flatMap_cons,List.foldl_append]
    rw [show bits d=[d.noise₀,d.noise₁,d.coin,d.noise₃] from rfl]
    rw [four_steps s m d.bound d.coin d.noise₀ d.noise₁ d.noise₃ _ hm]
    rw [ih]
    · rfl
    · simp [hm]

theorem pass_stacks (ds : List Digit) (m : Memory 4) (hm : m.stack 0=ds.map Digit.bound) :
    (wordMemory ds m).stack 0=[] ∧
    (wordMemory ds m).stack 1=(ds.map Digit.coin).reverse++m.stack 1 ∧
    (wordMemory ds m).stack 2=(ds.map Digit.bound).reverse++m.stack 2 ∧
    (wordMemory ds m).stack 3=m.stack 3 := by
  induction ds generalizing m with
  | nil => simp_all [wordMemory]
  | cons d ds ih =>
    have htail : (digitMemory m d.bound d.coin).stack 0=ds.map Digit.bound := by simp [hm]
    have hh := ih (digitMemory m d.bound d.coin) htail
    simpa [wordMemory,List.reverse_cons,List.append_assoc] using hh

 
theorem pass_length (ds : List Digit) : (ds.flatMap bits).length=4*ds.length := by
  induction ds with
  | nil => rfl
  | cons d ds ih => simp [bits,ih]; omega

theorem finish (s : Cmp) (m : Memory 4) (hn : m.stack 0=[]) (b₀ b₁ b₂ : Bool) :
    [b₀,b₁,b₂].foldl (fun c b => step program b c) (config (.start s) m)=
      ⟨none,(m.pop 0).push 3 (accept s)⟩ := by
  simp [List.foldl_cons,List.foldl_nil,step,program,label,config,code,effect,branch,hn]

end
end Contingency.BitModel.StackCode.BinaryTrial

 

 

open scoped BigOperators
namespace Contingency.BitModel.StackCode.BinaryTrial

def cmpNat (x y : ℕ) : Cmp := if x<y then .lt else if x=y then .eq else .gt

def beValue (xs : List Bool) : ℕ := xs.foldl (fun a b => 2*a+b.toNat) 0

theorem advance_cmpNat (x y : ℕ) (v b : Bool) :
    advance (cmpNat x y) v b=cmpNat (2*x+b.toNat) (2*y+v.toNat) := by
  cases v <;> cases b <;>
    unfold cmpNat <;> split_ifs <;> simp_all [advance] <;> omega

theorem cmp_fold (ds : List Digit) (x y : ℕ) :
    wordCmp ds (cmpNat x y)=
      cmpNat ((ds.map Digit.coin).foldl (fun n b => 2*n+b.toNat) x)
        ((ds.map Digit.bound).foldl (fun n b => 2*n+b.toNat) y) := by
  induction ds generalizing x y with
  | nil => rfl
  | cons d ds ih =>
    change wordCmp ds (advance (cmpNat x y) d.bound d.coin)=_
    rw [advance_cmpNat,ih]
    rfl

theorem comparison_correct (ds : List Digit) :
    accept (wordCmp ds .eq)=decide (beValue (ds.map Digit.coin)≤beValue (ds.map Digit.bound)) := by
  have hh : wordCmp ds .eq=cmpNat (beValue (ds.map Digit.coin))
      (beValue (ds.map Digit.bound)) := cmp_fold ds 0 0
  rw [hh]
  unfold cmpNat
  split_ifs <;> simp_all [accept] <;> omega

def wordValue {n : ℕ} (bs : Fin n → Bool) : ℕ := beValue (List.ofFn bs)

theorem wordValue_succ {n : ℕ} (bs : Fin (n+1) → Bool) :
    wordValue bs=2*wordValue (fun i : Fin n => bs i.castSucc)+(bs (Fin.last n)).toNat := by
  unfold wordValue beValue
  rw [List.ofFn_succ',List.concat_eq_append,List.foldl_append]
  rfl

theorem wordValue_lt {n : ℕ} (bs : Fin n → Bool) : wordValue bs<2^n := by
  induction n with
  | zero => simp [wordValue,beValue]
  | succ n ih =>
    have hh := ih (fun i => bs i.castSucc)
    rw [wordValue_succ,pow_succ]
    cases hb : bs (Fin.last n) <;> simp only [Bool.toNat_false,Bool.toNat_true] <;> omega

theorem wordValue_injective (n : ℕ) : Function.Injective (@wordValue n) := by
  induction n with
  | zero => intro f g _; funext i; exact Fin.elim0 i
  | succ n ih =>
    intro f g h
    rw [wordValue_succ,wordValue_succ] at h
    have hb : f (Fin.last n)=g (Fin.last n) := by
      cases hf : f (Fin.last n) <;> cases hg : g (Fin.last n) <;> try rfl
      all_goals simp only [hf,hg,Bool.toNat_true,Bool.toNat_false] at h; omega
    have hp : wordValue (fun i : Fin n => f i.castSucc)=wordValue (fun i : Fin n => g i.castSucc) := by
      rw [hb] at h; omega
    have hh := ih hp
    funext i
    exact Fin.lastCases hb (fun i => congrFun hh i) i

def wordFin {n : ℕ} (bs : Fin n → Bool) : Fin (2^n) := ⟨wordValue bs,wordValue_lt bs⟩

theorem wordFin_bijective (n : ℕ) : Function.Bijective (@wordFin n) := by
  apply (Fintype.bijective_iff_injective_and_card _).mpr
  constructor
  · intro f g h
    exact wordValue_injective n (congrArg Fin.val h)
  · simp

noncomputable def wordEquiv (n : ℕ) : (Fin n → Bool) ≃ Fin (2^n) :=
  Equiv.ofBijective wordFin (wordFin_bijective n)

 

theorem word_count (n : ℕ) (u : Fin (2^n)) :
    (Finset.univ.filter fun bs : Fin n → Bool => wordFin bs=u).card=1 := by
  classical
  change (Finset.univ.filter fun bs => wordEquiv n bs=u).card=1
  have hh (bs) : wordEquiv n bs=u ↔ bs=(wordEquiv n).symm u := by
    exact (Equiv.eq_symm_apply _).symm
  have he : Finset.univ.filter (fun bs => wordEquiv n bs=u) = {(wordEquiv n).symm u} := by
    ext bs
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_singleton,hh]
  rw [he,Finset.card_singleton]

end Contingency.BitModel.StackCode.BinaryTrial

end

end OAI
