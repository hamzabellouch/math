import OAI.Combinatorics.VariableWL.MultiStack

namespace OAI

universe uVariable1 uVariable2

namespace VariableWL.MultiStack
open Turing BoundedSimulation
variable (M : Machine)

def found (l : List (Γ M)) : Bool := l.contains 2

def drainVars (v : Vars M) (l : List (Γ M)) : Vars M :=
  { reads := Function.update v.reads 0 0
    data := none
    answer := v.answer || found M l }

def drainLabel (b : Bool) : Option (Label M) := if b then none else some (.drain true)

theorem drain_stage (b : Bool) (S : Stacks M) (v : Vars M) :
    Steps (TM2.step (program M)) ((S (0,b)).length+1)
      ⟨some (.drain b),v,S⟩
      ⟨drainLabel M b,drainVars M v (S (0,b)),Function.update S (0,b) []⟩ := by
  generalize he : S (0,b)=l
  induction l generalizing S v with
  | nil =>
    apply Steps.single
    simp only [TM2.step,program,TM2.stepAux,he,List.head?_nil,List.tail_nil,
      Option.isSome_none,reduceCtorEq,decide_false,Bool.or_false,
      Function.update_self,drainVars,found,List.contains_nil]
    cases b <;> rfl
  | cons a l ih =>
    let v' : Vars M :=
      { reads := Function.update v.reads 0 1
        data := none
        answer := v.answer || decide (a=2) }
    let S' : Stacks M := Function.update S (0,b) l
    have hs : TM2.step (program M) ⟨some (.drain b),v,S⟩=
        some ⟨some (.drain b),v',S'⟩ := by
      simp only [TM2.step,program,TM2.stepAux,he,List.head?_cons,List.tail_cons,
        Option.isSome_some,Function.update_self,Option.some.injEq]
      rfl
    have hh := ih S' v' (Function.update_self _ _ _)
    have hc : drainVars M v' l=drainVars M v (a::l) := by
      simp only [drainVars,v',Function.update_idem,found,List.contains_cons,Bool.or_assoc]
      congr 1
      have hd : decide (a=2)=(2==a) := by
        by_cases h : a=2
        · subst a; simp
        · have h' : (2 : Γ M) ≠ a := Ne.symm h
          simp [h,h']
      rw [hd]
    have hS : Function.update S' (0,b) []=Function.update S (0,b) [] := by
      exact Function.update_idem _ _ _
    simpa only [List.length_cons,hc,hS] using Steps.head hs hh

theorem drain_both (S : Stacks M) (v : Vars M) :
    ∃ s', Steps (TM2.step (program M)) ((S (0,false)).length+(S (0,true)).length+2)
      ⟨some (.drain false),v,S⟩ s' ∧ s'.l=none ∧
      s'.var.answer=(v.answer || (found M (S (0,false)) || found M (S (0,true)))) := by
  have h0 := drain_stage M false S v
  have h1 := drain_stage M true (Function.update S (0,false) []) (drainVars M v (S (0,false)))
  have hn : ((0 : K M),true) ≠ (0,false) := by simp
  rw [Function.update_of_ne hn] at h1
  have hh := h0.trans h1
  refine ⟨⟨none,drainVars M (drainVars M v (S (0,false))) (S (0,true)),
    Function.update (Function.update S (0,false) []) (0,true) []⟩,?_,rfl,?_⟩
  · have he : (S (0,false)).length+1+((S (0,true)).length+1)=
        (S (0,false)).length+(S (0,true)).length+2 := by omega
    simpa only [he,drainLabel,ite_true] using hh
  · simp only [drainVars,Bool.or_assoc]

end VariableWL.MultiStack

namespace VariableWL.MultiStack
open Turing BoundedSimulation
variable (M : Machine)

theorem exists_getI_two (l : List (Γ M)) : (∃ n, l.getI n=2) ↔ 2 ∈ l := by
  constructor
  · rintro ⟨n,hn⟩
    by_cases hl : n < l.length
    · rw [List.getI_eq_getElem _ hl] at hn
      exact hn ▸ List.getElem_mem hl
    · rw [List.getI_eq_default _ (by omega)] at hn
      have : (0 : Γ M)=2 := hn
      have hh := congrArg Fin.val this
      change 0=2 % (M.workSymbols+3) at hh
      rw [Nat.mod_eq_of_lt (by omega)] at hh
      omega
  · intro h
    obtain ⟨n,hn,he⟩ := List.mem_iff_getElem.mp h
    exact ⟨n,(List.getI_eq_getElem _ hn).trans he⟩

theorem tape_two_iff (S : Stacks M) (j : K M) : (∃ i, (tape M S j).nth i=2) ↔
    (found M (S (j,false)) || found M (S (j,true)))=true := by
  simp only [Bool.or_eq_true,found,List.contains_iff_mem]
  constructor
  · rintro ⟨i,hi⟩
    cases i with
    | ofNat n =>
      exact Or.inr ((exists_getI_two M _).mp ⟨n,(tape_nth_nat M S j n).symm.trans hi⟩)
    | negSucc n =>
      exact Or.inl ((exists_getI_two M _).mp ⟨n,hi⟩)
  · rintro (h | h)
    · obtain ⟨n,hn⟩ := (exists_getI_two M _).mpr h
      exact ⟨(-(n+1:ℕ):ℤ),hn⟩
    · obtain ⟨n,hn⟩ := (exists_getI_two M _).mpr h
      exact ⟨(n:ℤ),(tape_nth_nat M S j n).trans hn⟩

theorem symbol_zero_ne_two : (0 : Γ M) ≠ 2 := by
  intro h
  have hh := congrArg Fin.val h
  change 0=2 % (M.workSymbols+3) at hh
  rw [Nat.mod_eq_of_lt (by omega)] at hh
  omega

theorem symbol_one_ne_two : (1 : Γ M) ≠ 2 := by
  intro h
  have hh := congrArg Fin.val h
  change 1 % (M.workSymbols+3)=2 % (M.workSymbols+3) at hh
  rw [Nat.mod_eq_of_lt (by omega),Nat.mod_eq_of_lt (by omega)] at hh
  omega

theorem word_two_iff (b : Bool) : (∃ i, wordCells M.workSymbols [b] i=2) ↔ b=true := by
  constructor
  · rintro ⟨i,hi⟩
    unfold wordCells at hi
    split_ifs at hi with h
    · cases hn : i.toNat with
      | zero =>
        cases b with
        | false => exact (symbol_one_ne_two M (by simpa only [hn,List.getElem?_cons_zero] using hi)).elim
        | true => rfl
      | succ n => exact (symbol_zero_ne_two M (by simpa only [hn,List.getElem?_cons_succ,List.getElem?_nil] using hi)).elim
    · exact (symbol_zero_ne_two M hi).elim
  · rintro rfl
    exact ⟨0,rfl⟩

theorem related_output (c : Configuration M) (s : Config M) (h : Related M c s)
    (b : Bool) (hout : c.cells 0=wordCells M.workSymbols [b]) :
    (found M (s.stk (0,false)) || found M (s.stk (0,true)))=b := by
  apply Bool.eq_iff_iff.mpr
  rw [← tape_two_iff]
  have he : (∃ i, (tape M s.stk 0).nth i=2) ↔ ∃ i, wordCells M.workSymbols [b] i=2 := by
    constructor
    · rintro ⟨i,hi⟩
      rw [h.2,hout] at hi
      exact ⟨_,hi⟩
    · rintro ⟨i,hi⟩
      refine ⟨i-c.heads 0,?_⟩
      rw [h.2,hout]
      simpa only [add_sub_cancel] using hi
  exact he.trans (word_two_iff M b)

instance : Fintype Motion := ⟨{.left,.stay,.right},by intro m; cases m <;> simp⟩

instance : Fintype (Vars M) := Fintype.ofEquiv ((K M → Γ M) × Option (Data M) × Bool)
  ⟨(fun v => ⟨v.1,v.2.1,v.2.2⟩),(fun v => (v.reads,v.data,v.answer)),
    (by rintro ⟨a,b,c⟩; rfl),(by rintro ⟨a,b,c⟩; rfl)⟩

noncomputable def operationsBound : ℕ := Finset.univ.sup (fun l : Label M => StackSimulation.operations (program M l))

theorem operations_le (l : Label M) : StackSimulation.operations (program M l) ≤ operationsBound M :=
  Finset.le_sup (f := fun l : Label M => StackSimulation.operations (program M l)) (Finset.mem_univ l)

theorem outputs_simulated (w : Word) (b : Bool) (T : ℕ) (h : OutputsWithin M w [b] T) :
    ∃ n ≤ T+2*(w.length+T*operationsBound M)+3,
      ∃ s : Config M, Steps (TM2.step (program M)) n (initialConfig M w) s ∧
        s.l=none ∧ s.var.answer=b := by
  obtain ⟨t,ht,hhalt,hout⟩ := h
  obtain ⟨u,hu,hsteps⟩ := evolve_steps (step M) (initial M w) t
  rw [← run_eq_evolve] at hsteps
  obtain ⟨s,hs,hrel⟩ := simulate_steps M (initialConfig M w) (initial_related M w) hsteps
  have hlen := StackSimulation.evolve_length (program M) (operationsBound M) (operations_le M)
    (initialConfig M w) w.length (initial_lengths M w) u
  rw [hs.evolve] at hlen
  have hstop := simulate_halt M (run M w t) s hrel hhalt
  obtain ⟨s',hfinish,hl,ha⟩ := drain_both M s.stk
    {reads := scanned (run M w t), data := none, answer := false}
  have hh := hs.trans ((Steps.single hstop).trans hfinish)
  refine ⟨_,?_,s',hh,hl,?_⟩
  · have h0 := hlen (0,false)
    have h1 := hlen (0,true)
    have huT : u ≤ T := hu.trans ht
    have hc := Nat.mul_le_mul_right (operationsBound M) huT
    omega
  · rw [ha,Bool.false_or]
    exact related_output M (run M w t) s hrel b hout

end VariableWL.MultiStack

namespace VariableWL.TM0Adapter
open Turing BoundedSimulation
variable {Γ : Type uVariable1} {Λ : Type uVariable2} [Inhabited Γ] [Inhabited Λ]
variable (M : TM0.Machine Γ Λ) (S : Finset Λ) (hS : TM0.Supports M (S : Set Λ))

abbrev Control := {q : Λ // q ∈ S}

def action (a : Γ) : TM0.Stmt Γ → Γ × Motion
  | .move .left => (a,.left)
  | .move .right => (a,.right)
  | .write b => (b,.stay)

noncomputable def program (accept : Λ → Γ → Bool) : OneHead.Program (Control S) Γ where
  start := ⟨default,hS.1⟩
  transition := fun q a => match h : M q.val a with
    | none => none
    | some (q',s) => some (⟨q',hS.2 h q.property⟩,action a s)
  accepting := fun q a => accept q.val a

def Related (c : TM0.Cfg Γ Λ) (s : OneHead.State (Control S) Γ ℤ) : Prop :=
  s.control.val=c.q ∧ ∀ i, c.Tape.nth i=s.cells (s.head+i)

variable (accept : Λ → Γ → Bool)

omit [Inhabited Γ] in
theorem program_none (q : Control S) (a : Γ) (h : M q.val a=none) :
    (program M S hS accept).transition q a=none := by
  dsimp only [program]
  split <;> simp_all

omit [Inhabited Γ] in
theorem program_some (q : Control S) (a : Γ) (r : Λ) (t : TM0.Stmt Γ)
    (h : M q.val a=some (r,t)) :
    (program M S hS accept).transition q a=some (⟨r,hS.2 h q.property⟩,action a t) := by
  dsimp only [program]
  split
  · rename_i he
    rw [h] at he
    cases he
  · rename_i q' t' he
    have he' : (q',t')=(r,t) := Option.some.inj (he.symm.trans h)
    cases he'
    rfl

theorem next_related {c c' : TM0.Cfg Γ Λ} (s : OneHead.State (Control S) Γ ℤ)
    (hr : Related S c s) (hc : TM0.step M c=some c') :
    Related S c' ((program M S hS accept).next 1 s) := by
  have ha : s.cells s.head=c.Tape.1 := by simpa only [Tape.nth_zero,Int.add_zero] using (hr.2 0).symm
  obtain ⟨⟨q,t⟩,ht,rfl⟩ := Option.map_eq_some_iff.mp hc
  have ht' : M s.control.val (s.cells s.head)=some (q,t) := by rw [hr.1,ha]; exact ht
  have hp := program_some M S hS accept s.control (s.cells s.head) q t ht'
  constructor
  · simp only [OneHead.Program.next,OneHead.Program.action,hp,Option.getD_some]
  · intro i
    simp only [OneHead.Program.next,OneHead.Program.action,hp,Option.getD_some]
    cases t with
    | write b =>
      simp only [action,OneHead.move,Tape.write_nth,Function.update_apply]
      rw [hr.2]
      by_cases hi : i=0
      · subst i; simp
      · have hne : s.head+i ≠ s.head := by omega
        simp only [hi,hne,ite_false]
    | move d =>
      cases d <;>
        simp only [action,OneHead.move,Function.update_eq_self,Tape.move_left_nth,Tape.move_right_nth] <;>
        rw [hr.2] <;> congr 1 <;> omega

theorem steps_related {c c' : TM0.Cfg Γ Λ} {n : ℕ} (s : OneHead.State (Control S) Γ ℤ)
    (hr : Related S c s) (hc : Steps (TM0.step M) n c c') :
    Related S c' ((program M S hS accept).run 1 s n) := by
  induction hc generalizing s with
  | zero => exact hr
  | @succ n c c₁ c₂ ht hs ih =>
    have hh := ih ((program M S hS accept).next 1 s) (next_related M S hS accept s hr ht)
    rw [show n+1=1+n by omega,OneHead.run_add]
    exact hh

theorem halt_related {c : TM0.Cfg Γ Λ} (s : OneHead.State (Control S) Γ ℤ)
    (hr : Related S c s) (hc : TM0.step M c=none) :
    (program M S hS accept).transition s.control (s.cells s.head)=none := by
  have ha : s.cells s.head=c.Tape.1 := by simpa only [Tape.nth_zero,Int.add_zero] using (hr.2 0).symm
  apply program_none
  rw [hr.1,ha]
  exact Option.map_eq_none_iff.mp hc

theorem acceptance_related {c : TM0.Cfg Γ Λ} (s : OneHead.State (Control S) Γ ℤ)
    (hr : Related S c s) :
    (program M S hS accept).accepting s.control (s.cells s.head)=accept c.q c.Tape.1 := by
  change accept s.control.val (s.cells s.head)=_
  rw [hr.1]
  congr 1
  simpa only [Tape.nth_zero,Int.add_zero] using (hr.2 0).symm

theorem initial_related (w : List Γ) :
    Related S (TM0.init w) (OneHead.lineInitial (program M S hS accept) default (fun j : Fin w.length => w[j])) := by
  refine ⟨rfl,?_⟩
  intro i
  change (Tape.mk₁ w).nth i=OneHead.lineInput default (fun j : Fin w.length => w[j]) (0+i)
  rw [Int.zero_add]
  cases i with
  | ofNat n =>
    change (Tape.mk₁ w).nth (n : ℤ)=OneHead.lineInput default (fun j : Fin w.length => w[j]) (n : ℤ)
    simp only [Tape.mk₁,Tape.mk₂,Tape.mk'_nth_nat,ListBlank.nth_mk,
      OneHead.lineInput,Int.natCast_nonneg,true_and,Int.toNat_natCast]
    by_cases hn : n < w.length
    · have hc : (n : ℤ) < w.length := by omega
      simp only [dite_eq_left hc,List.getI_eq_getElem _ hn]
      rfl
    · have hc : ¬ (n : ℤ) < w.length := by omega
      simp only [dite_eq_right hc,List.getI_eq_default w (show w.length ≤ n by omega)]
  | negSucc n =>
    have hn : ¬ (0 : ℤ) ≤ Int.negSucc n := by omega
    change default=OneHead.lineInput default (fun j : Fin w.length => w[j]) (Int.negSucc n)
    simp only [OneHead.lineInput,hn,false_and,dite_false]

end VariableWL.TM0Adapter

namespace VariableWL.MachineOneHead
open Turing BoundedSimulation
variable (M : Machine)

abbrev Alphabet := TM2to1.Γ' (MultiStack.Slot M) (fun _ => MultiStack.Γ M)
abbrev Label1 := TM2to1.Λ' (MultiStack.Slot M) (fun _ => MultiStack.Γ M)
  (MultiStack.Label M) (MultiStack.Vars M)
noncomputable def program1 := TM2to1.tr (MultiStack.program M)
noncomputable def support1 : Finset (Label1 M) := TM2to1.trSupp (MultiStack.program M) Finset.univ

theorem supported2 : TM2.Supports (MultiStack.program M) Finset.univ := by
  refine ⟨Finset.mem_univ _,fun q _ => ?_⟩
  generalize MultiStack.program M q=t
  induction t <;> simp_all [TM2.SupportsStmt]

theorem supported1 : TM1.Supports (program1 M) (support1 M) :=
  TM2to1.tr_supports (MultiStack.program M) (supported2 M)

abbrev Label0 := TM1to0.Λ' (program1 M)
noncomputable def program0 := TM1to0.tr (program1 M)
noncomputable def support0 : Finset (Label0 M) := TM1to0.trStmts (program1 M) (support1 M)
theorem supported0 : TM0.Supports (program0 M) (support0 M : Set (Label0 M)) :=
  TM1to0.tr_supports (program1 M) (supported1 M)

abbrev Control := TM0Adapter.Control (support0 M)
noncomputable instance : Fintype (Control M) := Fintype.ofFinite _

noncomputable def instructionsBound : ℕ := (support1 M).sup (fun l => UnitSimulation.instructions (program1 M l))
theorem instructions_le (l : Label1 M) (hl : l ∈ support1 M) :
    UnitSimulation.instructions (program1 M l) ≤ instructionsBound M :=
  Finset.le_sup (f := fun l => UnitSimulation.instructions (program1 M l)) hl

noncomputable def oneHead : OneHead.Program (Control M) (Alphabet M) :=
  TM0Adapter.program (program0 M) (support0 M) (supported0 M) (fun q _ => !q.2.answer)

noncomputable def input (w : Word) : List (Alphabet M) :=
  TM2to1.trInit (0,true) (w.map (MultiStack.inputSymbol M))

theorem input_pos (w : Word) : 0 < (input M w).length := Nat.succ_pos _

theorem input_length (w : Word) : (input M w).length ≤ w.length+1 := by
  change (((w.map (MultiStack.inputSymbol M)).reverse.map
    (fun a => (false,Function.update (fun _ : MultiStack.Slot M => none) (0,true) (some a)))).tail).length+1 ≤ w.length+1
  simp only [List.length_tail,List.length_map,List.length_reverse]
  omega

noncomputable def stackTime (m T : ℕ) : ℕ := T+2*(m+T*MultiStack.operationsBound M)+3
noncomputable def time (m T : ℕ) : ℕ :=
  stackTime M m T * (1+MultiStack.operationsBound M *
    (2*(m+stackTime M m T*MultiStack.operationsBound M+MultiStack.operationsBound M)+2)) * instructionsBound M

 theorem outputs_oneHead (w : Word) (b : Bool) (T : ℕ) (h : OutputsWithin M w [b] T) :
    ∃ t ≤ time M w.length T,
      (oneHead M).transition ((oneHead M).run 1
        (OneHead.lineInitial (oneHead M) default (fun j : Fin (input M w).length => (input M w)[j])) t).control
        (((oneHead M).run 1
        (OneHead.lineInitial (oneHead M) default (fun j : Fin (input M w).length => (input M w)[j])) t).cells
          ((oneHead M).run 1
        (OneHead.lineInitial (oneHead M) default (fun j : Fin (input M w).length => (input M w)[j])) t).head)=none ∧
      (oneHead M).accepting ((oneHead M).run 1
        (OneHead.lineInitial (oneHead M) default (fun j : Fin (input M w).length => (input M w)[j])) t).control
        (((oneHead M).run 1
        (OneHead.lineInitial (oneHead M) default (fun j : Fin (input M w).length => (input M w)[j])) t).cells
          ((oneHead M).run 1
        (OneHead.lineInitial (oneHead M) default (fun j : Fin (input M w).length => (input M w)[j])) t).head)= !b := by
  obtain ⟨n,hn,s,hs,hl,ha⟩ := MultiStack.outputs_simulated M w b T h
  have hinit := TM2to1.trCfg_init (K := MultiStack.Slot M) (Γ := fun _ => MultiStack.Γ M) (Λ := MultiStack.Label M) (σ := MultiStack.Vars M)
    (0,true) (w.map (MultiStack.inputSymbol M))
  obtain ⟨d,hd,u,hu,hrun⟩ := StackSimulation.run_bound (MultiStack.program M)
    (MultiStack.operationsBound M) (MultiStack.operations_le M) (MultiStack.initialConfig M w)
    (TM1.init (input M w)) hinit w.length (MultiStack.initial_lengths M w) n
  rw [hs.evolve] at hd
  have hdl : d.l=none := by cases hd; simpa only [Option.map_eq_none_iff] using hl
  have hdv : d.var=s.var := by cases hd; rfl
  have hi : (TM1.init (input M w) : TM1.Cfg (Alphabet M) (Label1 M) (MultiStack.Vars M)).l
      ∈ Finset.insertNone (support1 M) := Finset.some_mem_insertNone.mpr (supported1 M).1
  obtain ⟨t,ht,hunit⟩ := UnitSimulation.steps_bound (program1 M) (support1 M) (supported1 M)
    (instructionsBound M) (instructions_le M) hrun hi
  have hr := TM0Adapter.steps_related (program0 M) (support0 M) (supported0 M)
    (fun q _ => !q.2.answer) _ (TM0Adapter.initial_related (program0 M) (support0 M) (supported0 M)
      (fun q _ => !q.2.answer) (input M w)) hunit
  have hhalt : TM0.step (program0 M) (TM1to0.trCfg (program1 M) d)=none := by
    simp only [TM0.step,TM1to0.trCfg,program0,TM1to0.tr,hdl,Option.map_none]
  refine ⟨t,?_,TM0Adapter.halt_related _ _ _ _ _ hr hhalt,?_⟩
  · apply ht.trans
    apply Nat.mul_le_mul_right
    apply hu.trans
    apply Nat.mul_le_mul hn
    apply Nat.add_le_add_left
    apply Nat.mul_le_mul_left
    apply Nat.add_le_add_right
    apply Nat.mul_le_mul_left
    exact Nat.add_le_add_right (Nat.add_le_add_left (Nat.mul_le_mul_right _ hn) _) _
  · exact (TM0Adapter.acceptance_related _ _ _ _ _ hr).trans (by
      change (! d.var.answer)= !b
      rw [hdv,ha])

end VariableWL.MachineOneHead

end OAI
