import OAI.Computability.Scheduling.SchedulingAlgorithm

namespace OAI

section

namespace ThreeMachine.StackCompiler

inductive Action
  | stay
  | pop
  | push (b : Bool)
  deriving DecidableEq, Fintype

def Action.apply : Action → List Bool → List Bool
  | .stay, xs => xs
  | .pop, xs => xs.tail
  | .push b, xs => b :: xs

abbrev Store (k : ℕ) := Fin (k+1) → List Bool
abbrev Heads (k : ℕ) := Fin (k+1) → Option Bool
abbrev Actions (k : ℕ) := Fin (k+1) → Action

structure Program (k : ℕ) (Q : Type) where
  initial : Q
  transition : Q → Heads k → Option (Q × Actions k)

structure State (k : ℕ) (Q : Type) where
  control : Q
  store : Store k

def Program.step {k Q} (P : Program k Q) (c : State k Q) : Option (State k Q) := do
  let (q,a) ← P.transition c.control (fun i => (c.store i).head?)
  return ⟨q, fun i => (a i).apply (c.store i)⟩

def Program.run {k Q} (P : Program k Q) (s : Store k) (t : ℕ) : State k Q :=
  (fun c => (P.step c).getD c)^[t] ⟨P.initial,s⟩

def Program.Computes {k Q} (P : Program k Q) (s t : Store k) (bound : ℕ) : Prop :=
  ∃ n ≤ bound, (P.run s n).store = t ∧ P.step (P.run s n) = none

def symbol (b : Bool) : Fin 3 := bitSymbol b

def unsymbol (a : Fin 3) : Option Bool :=
  if a = 0 then none else some (a = 2)

@[simp] theorem unsymbol_symbol (b : Bool) : unsymbol (symbol b) = some b := by
  cases b <;> decide

@[simp] theorem unsymbol_zero : unsymbol 0 = none := rfl

def stackTape (xs : List Bool) : Turing.Tape (Fin 3) :=
  Turing.Tape.mk₁ (xs.map symbol)

theorem head_stackTape (xs : List Bool) : unsymbol (stackTape xs).head = xs.head? := by
  cases xs with
  | nil => rfl
  | cons b xs => exact unsymbol_symbol b

def phaseOne (a : Action) (head : Fin 3) : Fin 3 × Option Turing.Dir :=
  match a with
  | .stay => (head,none)
  | .pop => (0,some .right)
  | .push _ => (head,some .left)

def phaseTwo (a : Action) (head : Fin 3) : Fin 3 × Option Turing.Dir :=
  match a with
  | .push b => (symbol b,none)
  | _ => (head,none)

def applyTape (a : Fin 3 × Option Turing.Dir) (t : Turing.Tape (Fin 3)) :
    Turing.Tape (Fin 3) :=
  match a.2 with
  | none => t.write a.1
  | some d => (t.write a.1).move d

def middleTape (a : Action) (xs : List Bool) : Turing.Tape (Fin 3) :=
  applyTape (phaseOne a (stackTape xs).head) (stackTape xs)

@[simp] theorem blank_cons :
    (Turing.ListBlank.mk ([] : List (Fin 3))).cons 0 = Turing.ListBlank.mk [] := by
  exact Turing.ListBlank.cons_head_tail (Turing.ListBlank.mk [])

theorem tape_two_phases (a : Action) (xs : List Bool) :
    applyTape (phaseTwo a (middleTape a xs).head) (middleTape a xs) = stackTape (a.apply xs) := by
  cases a with
  | stay => simp [applyTape, phaseTwo, middleTape, phaseOne, Action.apply]
  | pop =>
    change (((stackTape xs).write 0).move .right).write
      (((stackTape xs).write 0).move .right).head = stackTape xs.tail
    rw [Turing.Tape.write_self]
    simp only [stackTape, Turing.Tape.mk₁, Turing.Tape.mk₂, Turing.Tape.write_mk',
      Turing.Tape.move_right_mk', Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons,
      blank_cons]
    cases xs <;> rfl
  | push b =>
    change (((stackTape xs).write (stackTape xs).head).move .left).write (symbol b) =
      stackTape (b :: xs)
    rw [Turing.Tape.write_self]
    simp only [stackTape, Turing.Tape.mk₁, Turing.Tape.mk₂, Turing.Tape.move_left_mk',
      Turing.Tape.write_mk', Turing.ListBlank.tail_mk,
      List.tail_nil, List.tail_cons, List.map_cons, Turing.ListBlank.cons_mk]

abbrev Control (k : ℕ) (Q : Type) := Q ⊕ (Q × Actions k)

section Compilation
variable {k : ℕ} {Q : Type} [Fintype Q] (P : Program k Q)

noncomputable def numberControl (q : Control k Q) : Fin (Fintype.card (Control k Q) + 1) :=
  (Fintype.equivFin (Control k Q) q).succ

noncomputable def readControl (i : Fin (Fintype.card (Control k Q) + 1)) : Control k Q :=
  if h : i.val = 0 then .inl P.initial else
    (Fintype.equivFin (Control k Q)).symm ⟨i.val-1, by have := i.isLt; omega⟩

@[simp] theorem read_numberControl (q : Control k Q) : readControl P (numberControl q) = q := by
  simp [readControl, numberControl]

@[simp] theorem read_zero : readControl P 0 = .inl P.initial := by
  simp [readControl]

noncomputable def compile : Machine k (Fintype.card (Control k Q)) 0 where
  transition i heads :=
    match readControl P i with
    | .inl q => (P.transition q (fun j => unsymbol (heads j))).map
        (fun qa => (numberControl (.inr qa), fun j => phaseOne (qa.2 j) (heads j)))
    | .inr qa => some (numberControl (.inl qa.1), fun j => phaseTwo (qa.2 j) (heads j))

abbrev TapeCfg := Configuration k (Fintype.card (Control k Q)) 0

def Relates (c : TapeCfg (k := k) (Q := Q)) (s : State k Q) : Prop :=
  readControl P c.state = .inl s.control ∧ ∀ j, c.tapes j = stackTape (s.store j)

noncomputable def middleCfg (qa : Q × Actions k) (s : Store k) : TapeCfg (k := k) (Q := Q) :=
  ⟨numberControl (.inr qa), fun j => middleTape (qa.2 j) (s j)⟩

noncomputable def readyCfg (s : State k Q) : TapeCfg (k := k) (Q := Q) :=
  ⟨numberControl (.inl s.control), fun j => stackTape (s.store j)⟩

@[simp] theorem relates_ready (s : State k Q) : Relates P (readyCfg s) s :=
  ⟨read_numberControl P _, fun _ => rfl⟩

theorem step_ready {c : TapeCfg (k := k) (Q := Q)} {s : State k Q}
    (h : Relates P c s) :
    (compile P).step c =
      (P.transition s.control (fun j => (s.store j).head?)).map (fun qa => middleCfg qa s.store) := by
  have ht : (fun j => unsymbol (c.tapes j).head) = fun j => (s.store j).head? := by
    funext j
    rw [h.2 j, head_stackTape]
  unfold Machine.step compile
  simp only [h.1, ht]
  cases he : P.transition s.control (fun j => (s.store j).head?) with
  | none => rfl
  | some qa =>
    apply congrArg some
    congr 1
    funext j
    dsimp only
    rw [h.2 j]
    rfl

theorem step_middle (qa : Q × Actions k) (s : Store k) :
    (compile P).step (middleCfg qa s) =
      some (readyCfg ⟨qa.1,fun j => (qa.2 j).apply (s j)⟩) := by
  unfold Machine.step compile middleCfg
  simp only [read_numberControl]
  apply congrArg some
  congr 1
  funext j
  exact tape_two_phases (qa.2 j) (s j)

theorem halted_iff {c : TapeCfg (k := k) (Q := Q)} {s : State k Q}
    (h : Relates P c s) : (compile P).step c = none ↔ P.step s = none := by
  rw [step_ready P h]
  unfold Program.step
  cases P.transition s.control (fun j => (s.store j).head?) <;> simp

theorem two_steps {c : TapeCfg (k := k) (Q := Q)} {s : State k Q}
    (h : Relates P c s) :
    Relates P ((fun d => ((compile P).step d).getD d)^[2] c) ((P.step s).getD s) := by
  rw [Function.iterate_succ_apply, Function.iterate_succ_apply, Function.iterate_zero_apply]
  rw [step_ready P h]
  cases he : P.transition s.control (fun j => (s.store j).head?) with
  | none =>
    simp only [Option.map_none, Option.getD_none]
    rw [step_ready P h, he]
    simpa [Program.step, he] using h
  | some qa =>
    simp only [Option.map_some, Option.getD_some, step_middle]
    simp [Program.step, he]

theorem simulate {c : TapeCfg (k := k) (Q := Q)} {s : State k Q}
    (h : Relates P c s) (n : ℕ) :
    Relates P ((fun d => ((compile P).step d).getD d)^[2*n] c)
      ((fun d => (P.step d).getD d)^[n] s) := by
  induction n with
  | zero => exact h
  | succ n ih =>
    rw [Nat.mul_succ, Nat.add_comm (2*n) 2, Function.iterate_add_apply]
    simpa only [Function.iterate_succ_apply'] using two_steps P ih

def initialStore (input : List Bool) : Store k := fun i => if i = 0 then input else []

theorem relates_initial (input : List Bool) :
    Relates P ((compile P).initial input) ⟨P.initial, initialStore input⟩ := by
  refine ⟨read_zero P, ?_⟩
  intro i
  change Turing.Tape.mk₁ (if i = 0 then input.map bitSymbol else []) =
    Turing.Tape.mk₁ ((if i = 0 then input else []).map symbol)
  split_ifs <;> rfl

theorem simulate_initial (input : List Bool) (n : ℕ) :
    Relates P ((compile P).run input (2*n)) (P.run (initialStore input) n) :=
  simulate P (relates_initial P input) n

theorem compile_produces (input out : List Bool) (bound : ℕ)
    (h : ∃ n ≤ bound, P.step (P.run (initialStore input) n) = none ∧
      (P.run (initialStore input) n).store 0 = out) :
    (compile P).Produces input out (2*bound) := by
  obtain ⟨n,hn,hh,ho⟩ := h
  have hs := simulate_initial P input n
  refine ⟨2*n, by omega, (halted_iff P hs).mpr hh, ?_⟩
  rw [hs.2 0, ho]
  exact Turing.Tape.mk'_right₀ _ _

end Compilation
namespace Program
variable {k : ℕ} {Q R S : Type}

inductive Exec (P : Program k Q) : State k Q → ℕ → State k Q → Prop
  | halt {s} : P.step s = none → Exec P s 0 s
  | next {s t u n} : P.step s = some t → Exec P t n u → Exec P s (n+1) u

theorem Exec.iterate {P : Program k Q} {s t : State k Q} {n : ℕ}
    (h : Exec P s n t) : (fun c => (P.step c).getD c)^[n] s = t := by
  induction h with
  | halt => rfl
  | next he _ ih => simpa only [Function.iterate_succ_apply, he, Option.getD_some] using ih

theorem Exec.halted {P : Program k Q} {s t : State k Q} {n : ℕ}
    (h : Exec P s n t) : P.step t = none := by
  induction h with
  | halt h => exact h
  | next _ _ ih => exact ih

def State.mapControl (f : Q → R) (s : State k Q) : State k R := ⟨f s.control,s.store⟩

theorem Exec.continue {P : Program k Q} {P' : Program k R} (f : Q → R)
    (hs : ∀ s t, P.step s = some t →
      P'.step (State.mapControl f s) = some (State.mapControl f t))
    {s t : State k Q} {u : State k R} {n m : ℕ} (h : Exec P s n t)
    (ht : Exec P' (State.mapControl f t) m u) :
    Exec P' (State.mapControl f s) (n+m) u := by
  induction h with
  | halt => simpa only [Nat.zero_add] using ht
  | next he _ ih => simpa only [Nat.add_right_comm] using Exec.next (hs _ _ he) (ih ht)

theorem lift_step (P : Program k Q) (P' : Program k R) (f : Q → R)
    (h : ∀ q heads q' a, P.transition q heads = some (q',a) →
      P'.transition (f q) heads = some (f q',a))
    (s t : State k Q) (he : P.step s = some t) :
    P'.step (State.mapControl f s) = some (State.mapControl f t) := by
  unfold step at he
  cases hh : P.transition s.control (fun i => (s.store i).head?) with
  | none => simp [hh] at he
  | some qa =>
    have het : t = ⟨qa.1,fun i => (qa.2 i).apply (s.store i)⟩ := by
      simpa [hh] using he.symm
    subst t
    simp [step, State.mapControl, h _ _ _ _ hh]

def stayActions : Actions k := fun _ => .stay

def seq (P : Program k Q) (P' : Program k R) : Program k (Q ⊕ R) where
  initial := .inl P.initial
  transition q heads := match q with
    | .inl q => match P.transition q heads with
      | none => some (.inr P'.initial,stayActions)
      | some qa => some (.inl qa.1,qa.2)
    | .inr q => (P'.transition q heads).map (fun qa => (.inr qa.1,qa.2))

theorem seq_left_step (P : Program k Q) (P' : Program k R)
    (s t : State k Q) (h : P.step s = some t) :
    (seq P P').step (State.mapControl Sum.inl s) = some (State.mapControl Sum.inl t) := by
  apply lift_step P (seq P P') Sum.inl _ s t h
  intro q heads q' a ha
  simp [seq,ha]

theorem seq_right_exec (P : Program k Q) {P' : Program k R}
    {s t : State k R} {n : ℕ} (h : Exec P' s n t) :
    Exec (seq P P') (State.mapControl Sum.inr s) n (State.mapControl Sum.inr t) := by
  induction h with
  | halt he =>
    apply Exec.halt
    unfold step at he ⊢
    cases hh : P'.transition s.control (fun i => (s.store i).head?) <;> simp_all [seq,State.mapControl]
  | next he _ ih =>
    apply Exec.next _ ih
    apply lift_step P' (seq P P') Sum.inr _ _ _ he
    intro q heads q' a ha
    simp [seq, ha]

theorem seq_exec {P : Program k Q} {P' : Program k R} {s t : Store k}
    {q : Q} {r : R} {n m : ℕ} (h : Exec P ⟨P.initial,s⟩ n ⟨q,t⟩)
    {u : Store k} (h' : Exec P' ⟨P'.initial,t⟩ m ⟨r,u⟩) :
    Exec (seq P P') ⟨(seq P P').initial,s⟩ (n+m+1) ⟨Sum.inr r,u⟩ := by
  have hh := h.halted
  have hs : (seq P P').step ⟨Sum.inl q,t⟩ = some ⟨Sum.inr P'.initial,t⟩ := by
    unfold step at hh ⊢
    cases ht : P.transition q (fun i => (t i).head?) <;> simp_all [seq, stayActions,Action.apply]
  have hx := h.continue Sum.inl (seq_left_step P P') (Exec.next hs (seq_right_exec P h'))
  simpa only [State.mapControl, seq, Nat.add_assoc] using hx

def instruction (a : Heads k → Actions k) : Program k Bool where
  initial := false
  transition q h := if q then none else some (true,a h)

theorem instruction_exec (a : Heads k → Actions k) (s : Store k) :
    Exec (instruction a) ⟨false,s⟩ 1
      ⟨true,fun i => (a (fun j => (s j).head?) i).apply (s i)⟩ := by
  apply Exec.next (by rfl)
  exact Exec.halt rfl

def loop (test : Heads k → Bool) (P : Program k Q) : Program k (Option Q) where
  initial := none
  transition q h := match q with
    | none => if test h then some (some P.initial,stayActions) else none
    | some q => match P.transition q h with
      | none => some (none,stayActions)
      | some qa => some (some qa.1,qa.2)

theorem loop_body_step (test : Heads k → Bool) (P : Program k Q)
    (s t : State k Q) (h : P.step s = some t) :
    (loop test P).step (State.mapControl some s) = some (State.mapControl some t) := by
  apply lift_step P (loop test P) some _ s t h
  intro q heads q' a ha
  simp [loop,ha]

theorem loop_stop (test : Heads k → Bool) (P : Program k Q) (s : Store k)
    (h : test (fun i => (s i).head?) = false) :
    Exec (loop test P) ⟨none,s⟩ 0 ⟨none,s⟩ := by
  exact Exec.halt (by simp [step,loop,h])

theorem loop_iterate (test : Heads k → Bool) {P : Program k Q} {s t u : Store k}
    {q : Q} {n m : ℕ} (hs : test (fun i => (s i).head?) = true)
    (h : Exec P ⟨P.initial,s⟩ n ⟨q,t⟩)
    (hrest : Exec (loop test P) ⟨none,t⟩ m ⟨none,u⟩) :
    Exec (loop test P) ⟨none,s⟩ (n+m+2) ⟨none,u⟩ := by
  have hstart : (loop test P).step ⟨none,s⟩ = some ⟨some P.initial,s⟩ := by
    simp [step,loop,hs,stayActions,Action.apply]
  have hhalt := h.halted
  have hend : (loop test P).step ⟨some q,t⟩ = some ⟨none,t⟩ := by
    unfold step at hhalt ⊢
    cases ht : P.transition q (fun i => (t i).head?) <;>
      simp_all [loop,stayActions,Action.apply]
  have hb := h.continue some (loop_body_step test P) (Exec.next hend hrest)
  convert Exec.next hstart hb using 1

end Program
end ThreeMachine.StackCompiler

namespace ThreeMachine.StackCompiler
namespace Program
variable {k : ℕ}

def transferActions (src dst : Fin (k+1)) (h : Heads k) : Actions k := fun i =>
  if i = src then .pop else if i = dst then .push ((h src).getD false) else .stay

def transfer (src dst : Fin (k+1)) : Program k (Option Bool) :=
  loop (fun h => (h src).isSome) (instruction (transferActions src dst))

def transferResult (src dst : Fin (k+1)) (s : Store k) : Store k :=
  Function.update (Function.update s src []) dst ((s src).reverse ++ s dst)

def transferOnce (src dst : Fin (k+1)) (b : Bool) (xs : List Bool) (s : Store k) : Store k :=
  Function.update (Function.update s src xs) dst (b :: s dst)

theorem transfer_instruction {src dst : Fin (k+1)} (hne : src ≠ dst)
    (b : Bool) (xs : List Bool) (s : Store k) (hs : s src = b :: xs) :
    Exec (instruction (transferActions src dst)) ⟨false,s⟩ 1
      ⟨true,transferOnce src dst b xs s⟩ := by
  have h := instruction_exec (transferActions src dst) s
  convert h using 1
  congr 1
  funext i
  by_cases hi : i = src
  · subst i
    simp [transferOnce, transferActions, hne, hs, Action.apply]
  · by_cases hd : i = dst
    · subst i
      simp [transferOnce, transferActions, hne.symm, hs, Action.apply]
    · simp [transferOnce, transferActions,hi,hd,Action.apply]

theorem transfer_result_once {src dst : Fin (k+1)} (hne : src ≠ dst)
    (b : Bool) (xs : List Bool) (s : Store k) (hs : s src = b::xs) :
    transferResult src dst (transferOnce src dst b xs s) = transferResult src dst s := by
  funext i
  by_cases hi : i = dst
  · subst i
    simp [transferResult,transferOnce,hne,hs,List.reverse_cons,List.append_assoc]
  · by_cases hsrc : i = src
    · subst i
      simp [transferResult,transferOnce,hne]
    · simp [transferResult,transferOnce,hi,hsrc]

theorem transfer_exec {src dst : Fin (k+1)} (hne : src ≠ dst) (s : Store k) :
    Exec (transfer src dst) ⟨none,s⟩ (3*(s src).length) ⟨none,transferResult src dst s⟩ := by
  generalize he : s src = xs
  induction xs generalizing s with
  | nil =>
    have hr : transferResult src dst s = s := by
      funext i
      by_cases hd : i = dst
      · subst i; simp [transferResult,he]
      · by_cases hs : i = src
        · subst i; simp [transferResult,he,hne]
        · simp [transferResult,hd,hs]
    rw [hr]
    exact loop_stop _ _ s (by simp [he])
  | cons b xs ih =>
    let s' := transferOnce src dst b xs s
    have hs' : s' src = xs := by simp [s',transferOnce,hne]
    have hrest := ih s' hs'
    rw [transfer_result_once hne b xs s he] at hrest
    have hbody := transfer_instruction hne b xs s he
    have hx := loop_iterate (fun h => (h src).isSome) (by simp [he]) hbody hrest
    convert hx using 1 <;> first | rfl | simp only [List.length_cons]; omega

end Program
end ThreeMachine.StackCompiler

namespace ThreeMachine.StackCompiler.Program
variable {k : ℕ}

def popActions (src : Fin (k+1)) : Actions k := fun i => if i = src then .pop else .stay

def clear (src : Fin (k+1)) : Program k (Option Bool) :=
  loop (fun h => (h src).isSome) (instruction (fun _ => popActions src))

theorem pop_instruction (src : Fin (k+1)) (s : Store k) :
    Exec (instruction (fun _ => popActions src)) ⟨false,s⟩ 1
      ⟨true,Function.update s src (s src).tail⟩ := by
  convert instruction_exec (fun _ => popActions src) s using 1
  congr 1
  funext i
  by_cases h : i = src <;> simp [popActions,Action.apply,h]

theorem clear_exec (src : Fin (k+1)) (s : Store k) :
    Exec (clear src) ⟨none,s⟩ (3*(s src).length) ⟨none,Function.update s src []⟩ := by
  generalize he : s src = xs
  induction xs generalizing s with
  | nil =>
    have hr : Function.update s src [] = s := by rw [← he]; exact Function.update_eq_self _ _
    rw [hr]
    exact loop_stop _ _ s (by simp [he])
  | cons b xs ih =>
    let s' := Function.update s src xs
    have hrest := ih s' (by simp [s'])
    have hu : Function.update s' src [] = Function.update s src [] := by simp [s']
    rw [hu] at hrest
    have hbody : Exec (instruction (fun _ => popActions src)) ⟨false,s⟩ 1 ⟨true,s'⟩ := by
      simpa only [he,List.tail_cons] using pop_instruction src s
    have hx := loop_iterate (fun h => (h src).isSome) (by simp [he]) hbody hrest
    convert hx using 1 <;> first | rfl | simp only [List.length_cons]; omega

def spreadActions (src dst₁ dst₂ : Fin (k+1)) (h : Heads k) : Actions k := fun i =>
  if i = src then .pop else if i = dst₁ ∨ i = dst₂ then .push ((h src).getD false) else .stay

def spread (src dst₁ dst₂ : Fin (k+1)) : Program k (Option Bool) :=
  loop (fun h => (h src).isSome) (instruction (spreadActions src dst₁ dst₂))

def spreadResult (src dst₁ dst₂ : Fin (k+1)) (s : Store k) : Store k :=
  Function.update (Function.update (Function.update s src [])
    dst₁ ((s src).reverse ++ s dst₁)) dst₂ ((s src).reverse ++ s dst₂)

def spreadOnce (src dst₁ dst₂ : Fin (k+1)) (b : Bool) (xs : List Bool) (s : Store k) : Store k :=
  Function.update (Function.update (Function.update s src xs) dst₁ (b :: s dst₁)) dst₂ (b :: s dst₂)

theorem spread_instruction {src dst₁ dst₂ : Fin (k+1)}
    (h₁ : src ≠ dst₁) (h₂ : src ≠ dst₂) (h₃ : dst₁ ≠ dst₂)
    (b : Bool) (xs : List Bool) (s : Store k) (hs : s src = b :: xs) :
    Exec (instruction (spreadActions src dst₁ dst₂)) ⟨false,s⟩ 1
      ⟨true,spreadOnce src dst₁ dst₂ b xs s⟩ := by
  convert instruction_exec (spreadActions src dst₁ dst₂) s using 1
  congr 1
  funext i
  by_cases hi : i = src
  · subst i; simp [spreadOnce,spreadActions,h₁,h₂,hs,Action.apply]
  · by_cases hdi : i = dst₁
    · subst i; simp [spreadOnce,spreadActions,h₁.symm,h₃,hs,Action.apply]
    · by_cases hdj : i = dst₂
      · subst i; simp [spreadOnce,spreadActions,h₂.symm,hs,Action.apply]
      · simp [spreadOnce,spreadActions,hi,hdi,hdj,Action.apply]

theorem spread_result_once {src dst₁ dst₂ : Fin (k+1)}
    (h₁ : src ≠ dst₁) (h₂ : src ≠ dst₂) (h₃ : dst₁ ≠ dst₂)
    (b : Bool) (xs : List Bool) (s : Store k) (hs : s src = b::xs) :
    spreadResult src dst₁ dst₂ (spreadOnce src dst₁ dst₂ b xs s) = spreadResult src dst₁ dst₂ s := by
  funext i
  by_cases hi : i = dst₂
  · subst i
    simp [spreadResult,spreadOnce,h₁,h₂,hs,List.reverse_cons,List.append_assoc]
  · by_cases hd : i = dst₁
    · subst i
      simp [spreadResult,spreadOnce,h₁,h₂,h₃,hs,List.reverse_cons,List.append_assoc]
    · by_cases hsrc : i = src
      · subst i; simp [spreadResult,spreadOnce,h₁,h₂]
      · simp [spreadResult,spreadOnce,hi,hd,hsrc]

theorem spread_exec {src dst₁ dst₂ : Fin (k+1)}
    (h₁ : src ≠ dst₁) (h₂ : src ≠ dst₂) (h₃ : dst₁ ≠ dst₂) (s : Store k) :
    Exec (spread src dst₁ dst₂) ⟨none,s⟩ (3*(s src).length) ⟨none,spreadResult src dst₁ dst₂ s⟩ := by
  generalize he : s src = xs
  induction xs generalizing s with
  | nil =>
    have hr : spreadResult src dst₁ dst₂ s = s := by
      funext i
      by_cases hd₂ : i = dst₂
      · subst i; simp [spreadResult,he]
      · by_cases hd₁ : i = dst₁
        · subst i; simp [spreadResult,he,h₃]
        · by_cases hs : i = src
          · subst i; simp [spreadResult,he,h₁,h₂]
          · simp [spreadResult,hd₁,hd₂,hs]
    rw [hr]
    exact loop_stop _ _ s (by simp [he])
  | cons b xs ih =>
    let s' := spreadOnce src dst₁ dst₂ b xs s
    have hs' : s' src = xs := by simp [s',spreadOnce,h₁,h₂]
    have hrest := ih s' hs'
    rw [spread_result_once h₁ h₂ h₃ b xs s he] at hrest
    have hbody := spread_instruction h₁ h₂ h₃ b xs s he
    have hx := loop_iterate (fun h => (h src).isSome) (by simp [he]) hbody hrest
    convert hx using 1 <;> first | rfl | simp only [List.length_cons]; omega

def prepend (src dst tmp : Fin (k+1)) : Program k (Option Bool ⊕ Option Bool) :=
  seq (transfer src tmp) (spread tmp src dst)

theorem prepend_exec {src dst tmp : Fin (k+1)}
    (h₁ : src ≠ dst) (h₂ : src ≠ tmp) (h₃ : dst ≠ tmp)
    (s : Store k) (htmp : s tmp = []) :
    Exec (prepend src dst tmp) ⟨(prepend src dst tmp).initial,s⟩
      (6*(s src).length+1) ⟨Sum.inr none,Function.update s dst (s src ++ s dst)⟩ := by
  have hx := seq_exec (transfer_exec h₂ s)
    (spread_exec h₂.symm h₃.symm h₁ (transferResult src tmp s))
  have hl : (transferResult src tmp s tmp).length = (s src).length := by simp [transferResult,htmp]
  have he : spreadResult tmp src dst (transferResult src tmp s) =
      Function.update s dst (s src ++ s dst) := by
    funext i
    by_cases hd : i = dst
    · subst i; simp [spreadResult,transferResult,htmp,h₃,h₁.symm]
    · by_cases hsrc : i = src
      · subst i; simp [spreadResult,transferResult,htmp,h₂,h₁]
      · by_cases ht : i = tmp
        · subst i; simp [spreadResult,transferResult,htmp,h₂.symm,h₃.symm]
        · simp [spreadResult,transferResult,hd,hsrc,ht]
  rw [he,hl] at hx
  convert hx using 1 <;> first | rfl | omega

end ThreeMachine.StackCompiler.Program

namespace ThreeMachine.StackCompiler.Program
variable {k : ℕ}

def copy (src dst tmp : Fin (k+1)) : Program k (Option Bool ⊕ (Option Bool ⊕ Option Bool)) :=
  seq (clear dst) (prepend src dst tmp)

theorem copy_exec {src dst tmp : Fin (k+1)}
    (h₁ : src ≠ dst) (h₂ : src ≠ tmp) (h₃ : dst ≠ tmp)
    (s : Store k) (htmp : s tmp = []) :
    Exec (copy src dst tmp) ⟨(copy src dst tmp).initial,s⟩
      (3*(s dst).length+6*(s src).length+2)
      ⟨Sum.inr (Sum.inr none),Function.update s dst (s src)⟩ := by
  have hx := seq_exec (clear_exec dst s)
    (prepend_exec h₁ h₂ h₃ (Function.update s dst []) (by simp [h₃.symm,htmp]))
  simpa [copy,h₁,Nat.add_assoc] using hx

end ThreeMachine.StackCompiler.Program

end

end OAI
