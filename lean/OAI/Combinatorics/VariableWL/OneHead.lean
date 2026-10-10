import OAI.Combinatorics.VariableWL.Stack

namespace OAI

universe uVariable1 uVariable2 uVariable3 uVariable4 uVariable5 uVariable6 uVariable7 uVariable8 uVariable9 uVariable10

namespace VariableWL.Computation

variable {Q Γ : Type} {k : ℕ}

 theorem stackCells_pop (b : Bool) (w : Word) (i : ℤ) :
    (if i=stackHead (b::w) then none else stackCells (Γ:=Γ) (b::w) i)=stackCells w i := by
  rw [stackCells_cons]
  have hh : stackHead (b::w)=stackHead w-1 := by
    simp only [stackHead,List.length_cons]; omega
  rw [hh]
  split_ifs with h
  · subst i
    exact (stackCells_below w _ (by omega)).symm
  · rfl

namespace Stack

 def Machine.outputState (M : Machine Q k) (p remaining : Word) (ws : Fin (k+1) → Word) :
    Computation.State (Control Q k) PUnit (k+1) :=
  tapeState (some .output) p.length (typedWordCells p) (Function.update ws M.output remaining)

 theorem Machine.output_step (M : Machine Q k) (p remaining : Word) (b : Bool) (ws : Fin (k+1) → Word) :
    M.program.step (M.outputState p (b::remaining) ws)=some (M.outputState (p++[b]) remaining ws) := by
  unfold Program.step
  dsimp only [Machine.program,Machine.outputState,tapeState,Fin.cases_succ]
  rw [stackCells_head,Function.update_self,List.head?_cons,Option.bind_some,readBit_bit]
  apply congrArg some
  apply state_ext
  · rfl
  · funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · change (p.length:ℤ)+1=((p++[b]).length:ℤ)
      simp only [List.length_append,List.length_singleton,Nat.cast_add,Nat.cast_one]
    · change stackHead (Function.update ws M.output (b::remaining) j)+
        (if j=M.output then Motion.right else .stay).displacement=
        stackHead (Function.update ws M.output remaining j)
      by_cases h : j=M.output
      · subst j
        simp only [Function.update_self,ite_true,Motion.displacement,stackHead,List.length_cons]
        omega
      · simp only [Function.update_of_ne h,ite_eq_right h,Motion.displacement,add_zero]
  · funext i x
    refine Fin.cases ?_ (fun j => ?_) i
    · change (if x=p.length then bitSymbol b else typedWordCells p x)=typedWordCells (p++[b]) x
      exact (typedWordCells_snoc p b x).symm
    · change (if x=stackHead (Function.update ws M.output (b::remaining) j) then
        (if j=M.output then none else stackCells (Function.update ws M.output (b::remaining) j)
          (stackHead (Function.update ws M.output (b::remaining) j)))
        else stackCells (Function.update ws M.output (b::remaining) j) x)=
        stackCells (Function.update ws M.output remaining j) x
      by_cases h : j=M.output
      · subst j
        simp only [Function.update_self,ite_true]
        exact stackCells_pop b remaining x
      · simp only [Function.update_of_ne h,ite_eq_right h]
        split_ifs with hx
        · rw [hx]
        · rfl

 theorem Machine.output_all (M : Machine Q k) (p remaining : Word) (ws : Fin (k+1) → Word) :
    M.program.evolve (M.outputState p remaining ws) remaining.length=
      M.outputState (p++remaining) [] ws := by
  induction remaining generalizing p with
  | nil => simp only [List.length_nil,Program.evolve,List.append_nil]
  | cons b remaining ih =>
    rw [show (b::remaining).length=1+remaining.length by simp only [List.length_cons]; omega,
      Program.evolve_add,M.program.evolve_one (M.output_step p remaining b ws),ih]
    simp only [List.append_assoc,List.singleton_append]

 theorem Machine.output_halt (M : Machine Q k) (p : Word) (ws : Fin (k+1) → Word) :
    M.program.step (M.outputState p [] ws)=none := by
  unfold Program.step
  dsimp only [Machine.program,Machine.outputState,tapeState,Fin.cases_succ]
  rw [Function.update_self,stackCells_nil]
  rfl

 theorem Machine.execute_halt (M : Machine Q k) (s : State Q k) (h : M.step s=none) :
    M.program.step (M.execState s)=some (M.outputState [] (s.tapes M.output) s.tapes) := by
  have ht : M.transition s.control (fun j => (s.tapes j).head?)=none := by
    unfold Machine.step at h
    exact Option.map_eq_none_iff.mp h
  unfold Program.step
  dsimp only [Machine.program,Machine.execState,Fin.cases_succ]
  rw [show (fun j => readBit (stackCells (s.tapes j) (stackHead (s.tapes j))))=
      (fun j => (s.tapes j).head?) by funext j; rw [stackCells_head,readBit_bind],ht]
  apply congrArg some
  apply state_ext
  · rfl
  · funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · change stackHead (s.tapes j)+0=stackHead ((Function.update s.tapes M.output (s.tapes M.output)) j)
      rw [Function.update_eq_self,add_zero]
  · funext i x
    refine Fin.cases ?_ (fun j => ?_) i
    · change (if x=0 then none else none)=typedWordCells [] x
      simp only [ite_self,typedWordCells_nil]
    · change (if x=stackHead (s.tapes j) then stackCells (s.tapes j) (stackHead (s.tapes j))
        else stackCells (s.tapes j) x)=stackCells ((Function.update s.tapes M.output (s.tapes M.output)) j) x
      rw [Function.update_eq_self]
      split_ifs with hx
      · rw [hx]
      · rfl

 theorem Machine.execute_run (M : Machine Q k) (w : Word) (t : ℕ)
    (hno : ∀ u < t, M.step (M.run w u)≠none) :
    M.program.evolve (M.execState (M.initial w)) (2*t)=M.execState (M.run w t) := by
  induction t with
  | zero => rfl
  | succ t ih =>
    have ih' := ih (fun u hu => hno u (by omega))
    have hne := hno t (by omega)
    unfold Machine.step at hne
    have htrans : M.transition (M.run w t).control (fun j => ((M.run w t).tapes j).head?)≠none := by
      intro he
      apply hne
      rw [he]
      rfl
    obtain ⟨⟨q,acts⟩,ht⟩ := Option.ne_none_iff_exists'.mp htrans
    rw [show 2*(t+1)=2*t+2 by omega,Program.evolve_add,ih',M.execute_two (M.run w t) q acts ht]
    simp only [Machine.run,Machine.step,ht,Option.map_some,Option.getD_some]

 theorem Machine.compile_outputs (M : Machine Q k) {w out : Word} {T : ℕ}
    (h : M.OutputsWithin w out T) :
    M.program.OutputsWithin w out (4*(w.length+T+1)) := by
  obtain ⟨t,ht,halt,hout⟩ := h
  let haltPred := fun n => M.step (M.run w n)=none
  have hex : ∃ n, haltPred n := ⟨t,halt⟩
  let t₀ := Nat.find hex
  have ht₀ : t₀ ≤ t := Nat.find_min' hex halt
  have hstop : M.step (M.run w t₀)=none := Nat.find_spec hex
  have hn : ∀ u < t₀, M.step (M.run w u)≠none := by
    intro u hu
    exact Nat.find_min hex hu
  have stable {a : ℕ} (ha : M.step (M.run w a)=none) (n : ℕ) :
      M.run w (a+n)=M.run w a := by
    induction n with
    | zero => rfl
    | succ n ih =>
      change (M.step (M.run w (a+n))).getD (M.run w (a+n))=_
      rw [ih,ha]
      rfl
  have hout₀ : (M.run w t₀).tapes M.output=out := by
    have hs := stable hstop (t-t₀)
    rw [Nat.add_sub_of_le ht₀] at hs
    rw [← hs]
    exact hout
  have hlen : out.length ≤ w.length+t₀ := by
    rw [← hout₀]
    exact M.length_run w t₀ M.output
  let elapsed := 3*w.length+1+(2*t₀+(1+out.length))
  have hr : M.program.run w elapsed=M.outputState out [] (M.run w t₀).tapes := by
    rw [← Program.evolve_run]
    unfold elapsed
    rw [Program.evolve_add,Program.evolve_run,M.initialize,Program.evolve_add,
      M.execute_run w t₀ hn,Program.evolve_add,
      M.program.evolve_one (M.execute_halt (M.run w t₀) hstop),hout₀,M.output_all]
    rfl
  refine ⟨elapsed,by unfold elapsed; omega,?_,?_⟩
  · rw [hr]
    exact M.output_halt _ _
  · rw [hr]
    rfl

noncomputable def Machine.compile [Fintype Q] (M : Machine Q k) : VariableWL.Machine :=
  M.program.compile

 theorem Machine.outputs_compile [Fintype Q] (M : Machine Q k) {w out : Word} {T : ℕ}
    (h : M.OutputsWithin w out T) :
    VariableWL.OutputsWithin M.compile w out (4*(w.length+T+1)) :=
  M.program.compile_outputs (M.compile_outputs h)

end Stack
end VariableWL.Computation

namespace VariableWL.OneHead

variable {Q : Type uVariable1} {Γ : Type uVariable2} {A : Type uVariable3}

structure Program (Q : Type uVariable4) (Γ : Type uVariable5) where
  start : Q
  transition : Q → Γ → Option (Q × Γ × Motion)
  accepting : Q → Γ → Bool

structure State (Q : Type uVariable6) (Γ : Type uVariable7) (A : Type uVariable8) where
  control : Q
  head : A
  cells : A → Γ

abbrev Cell (Q : Type uVariable9) (Γ : Type uVariable10) := Γ × Option Q

def Program.action (M : Program Q Γ) (q : Q) (a : Γ) : Q × Γ × Motion :=
  (M.transition q a).getD (q,a,.stay)

def move [AddGroup A] (u : A) : Motion → A → A
  | .left, x => x-u
  | .stay, x => x
  | .right, x => x+u

def Program.next [AddGroup A] [DecidableEq A] (M : Program Q Γ) (u : A) (s : State Q Γ A) : State Q Γ A :=
  let a := M.action s.control (s.cells s.head)
  ⟨a.1, move u a.2.2 s.head, Function.update s.cells s.head a.2.1⟩

noncomputable def encode [DecidableEq A] (s : State Q Γ A) (i : A) : Cell Q Γ :=
  (s.cells i,if i=s.head then some s.control else none)

def Program.incoming (M : Program Q Γ) (m : Motion) (a : Cell Q Γ) : Option Q :=
  a.2.bind fun q => let b := M.action q a.1; if b.2.2=m then some b.1 else none

def Program.rule (M : Program Q Γ) (a b c : Cell Q Γ) : Cell Q Γ :=
  (b.2.elim b.1 (fun q => (M.action q b.1).2.1),
    (M.incoming .right a).or ((M.incoming .stay b).or (M.incoming .left c)))

theorem incoming_encode [DecidableEq A] (M : Program Q Γ) (s : State Q Γ A)
    (m : Motion) (i : A) : M.incoming m (encode s i) =
      if i=s.head ∧ (M.action s.control (s.cells s.head)).2.2=m
      then some (M.action s.control (s.cells s.head)).1 else none := by
  unfold Program.incoming encode
  by_cases h : i=s.head
  · subst i
    simp only [ite_true,Option.bind_some,true_and]
  · simp only [h,ite_false,Option.bind_none,false_and]

theorem rule_encode [AddCommGroup A] [DecidableEq A] (M : Program Q Γ)
    (u : A) (s : State Q Γ A) (i : A) :
    M.rule (encode s (i-u)) (encode s i) (encode s (i+u)) = encode (M.next u s) i := by
  apply Prod.ext
  · dsimp only [Program.rule,encode,Program.next]
    by_cases h : i=s.head
    · subst i
      simp only [ite_true,Option.elim_some,Function.update_self]
    · simp only [h,ite_false,Option.elim_none]
      exact (Function.update_of_ne h _ _).symm
  · change (M.incoming .right (encode s (i-u))).or
        ((M.incoming .stay (encode s i)).or (M.incoming .left (encode s (i+u)))) =
        if i=move u (M.action s.control (s.cells s.head)).2.2 s.head
        then some (M.action s.control (s.cells s.head)).1 else none
    rw [incoming_encode,incoming_encode,incoming_encode]
    cases h : (M.action s.control (s.cells s.head)).2.2 <;>
      simp only [move,reduceCtorEq,and_false,and_true,ite_false,Option.or_none,Option.none_or,
        sub_eq_iff_eq_add,eq_sub_iff_add_eq] <;> congr 1

noncomputable def Program.run [AddGroup A] [DecidableEq A] (M : Program Q Γ) (u : A) (s : State Q Γ A) : ℕ → State Q Γ A
  | 0 => s
  | t+1 => M.next u (M.run u s t)

noncomputable def evolution [AddGroup A] (u : A) (rule : Cell Q Γ → Cell Q Γ → Cell Q Γ → Cell Q Γ)
    (initial : A → Cell Q Γ) : ℕ → A → Cell Q Γ
  | 0 => initial
  | t+1 => fun i => rule (evolution u rule initial t (i-u))
      (evolution u rule initial t i) (evolution u rule initial t (i+u))

theorem evolution_encode [AddCommGroup A] [DecidableEq A] (M : Program Q Γ)
    (u : A) (s : State Q Γ A) (t : ℕ) :
    evolution u M.rule (encode s) t=encode (M.run u s t) := by
  induction t with
  | zero => rfl
  | succ t ih =>
    funext i
    simp only [evolution,ih,Program.run]
    exact rule_encode M u _ i

def Program.acceptingCell (M : Program Q Γ) (a : Cell Q Γ) : Prop :=
  ∃ q, a.2=some q ∧ M.accepting q a.1=true

theorem accepting_encode [DecidableEq A] (M : Program Q Γ) (s : State Q Γ A) :
    (∃ i, M.acceptingCell (encode s i)) ↔ M.accepting s.control (s.cells s.head)=true := by
  constructor
  · rintro ⟨i,q,hq,ha⟩
    by_cases hi : i=s.head
    · subst i
      have he : s.control=q := by simpa only [encode,ite_true,Option.some.injEq] using hq
      simpa only [encode,← he] using ha
    · simp only [encode,hi,ite_false] at hq
      cases hq
  · intro h
    exact ⟨s.head,s.control,by simp [encode],h⟩

theorem next_of_halt [AddGroup A] [DecidableEq A] (M : Program Q Γ) (u : A) (s : State Q Γ A)
    (h : M.transition s.control (s.cells s.head)=none) : M.next u s=s := by
  classical
  simp only [Program.next,Program.action,h,Option.getD_none,move,Function.update_eq_self]

theorem run_of_halt [AddGroup A] [DecidableEq A] (M : Program Q Γ) (u : A) (s : State Q Γ A)
    (h : M.transition s.control (s.cells s.head)=none) (t : ℕ) : M.run u s t=s := by
  induction t with
  | zero => rfl
  | succ t ih => rw [Program.run,ih,next_of_halt M u s h]

theorem run_add [AddGroup A] [DecidableEq A] (M : Program Q Γ) (u : A) (s : State Q Γ A) (a b : ℕ) :
    M.run u s (a+b)=M.run u (M.run u s a) b := by
  induction b with
  | zero => rfl
  | succ b ih =>
    change M.next u (M.run u s (a+b))=M.next u (M.run u (M.run u s a) b)
    rw [ih]

theorem run_freeze [AddGroup A] [DecidableEq A] (M : Program Q Γ) (u : A) (s : State Q Γ A) (a b : ℕ)
    (hab : a ≤ b) (h : M.transition (M.run u s a).control
      ((M.run u s a).cells (M.run u s a).head)=none) : M.run u s b=M.run u s a := by
  obtain ⟨c,rfl⟩ := Nat.exists_eq_add_of_le hab
  rw [run_add,run_of_halt M u _ h]

theorem head_bounds (M : Program Q Γ) (s : State Q Γ ℤ) (t : ℕ) :
    s.head-(t:ℤ) ≤ (M.run 1 s t).head ∧ (M.run 1 s t).head ≤ s.head+t := by
  induction t with
  | zero => simp [Program.run]
  | succ t ih =>
    change _ ≤ move 1 (M.action _ _).2.2 _ ∧ move 1 (M.action _ _).2.2 _ ≤ _
    cases (M.action (M.run 1 s t).control ((M.run 1 s t).cells (M.run 1 s t).head)).2.2 <;>
      simp only [move,Nat.cast_add,Nat.cast_one] <;> omega

end VariableWL.OneHead

end OAI
