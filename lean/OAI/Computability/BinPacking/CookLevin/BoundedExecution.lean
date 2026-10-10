import OAI.Computability.BinPacking.Computation.PoweringMachineRow

namespace OAI

namespace BinPackingGames.Foundations.Complexity.CookLevin.BoundedExecution

section Transition
variable {C : Type*}

def absorbingNext (step : C → Option C) (c : C) : C := (step c).getD c

@[simp] theorem absorbingNext_of_none (step : C → Option C) {c : C}
    (h : step c = none) : absorbingNext step c = c := by simp [absorbingNext, h]

@[simp] theorem absorbingNext_of_some (step : C → Option C) {c d : C}
    (h : step c = some d) : absorbingNext step c = d := by simp [absorbingNext, h]

private def advance (step : C → Option C) (c : Option C) : Option C := c.bind step

private theorem advance_iterate_none (step : C → Option C) (n : Nat) :
    (advance step)^[n] none = none := Function.iterate_fixed rfl n

theorem absorbing_of_successfulTrace (step : C → Option C) (n : Nat) (a b : C)
    (h : (fun c : Option C => c.bind step)^[n] (some a) = some b) :
    (absorbingNext step)^[n] a = b := by
  change (advance step)^[n] (some a) = some b at h
  induction n generalizing a with
  | zero => exact Option.some.inj h
  | succ n ih =>
    rw [Function.iterate_succ_apply] at h ⊢
    change (advance step)^[n] (step a) = some b at h
    cases hs : step a with
    | none =>
      rw [hs, advance_iterate_none] at h
      contradiction
    | some c =>
      rw [hs] at h
      rw [absorbingNext_of_some step hs]
      exact ih c h

def executionToAbsorbing (step : C → Option C) (a : C) (T : Nat) :
    StateTransition.EvalsToInTime step a (some ((absorbingNext step)^[T] a)) T := by
  induction T generalizing a with
  | zero => exact StateTransition.EvalsToInTime.refl step a
  | succ n ih =>
    cases hs : step a with
    | none =>
      have fixed : (absorbingNext step)^[n + 1] a = a :=
        Function.iterate_fixed (absorbingNext_of_none step hs) _
      exact {
        steps := 0
        evals_in_steps := by rw [fixed]; rfl
        steps_le_m := Nat.zero_le _ }
    | some b =>
      let first : StateTransition.EvalsToInTime step a (some b) 1 := {
        steps := 1
        evals_in_steps := by change step a = some b; exact hs
        steps_le_m := le_rfl }
      have full := StateTransition.EvalsToInTime.trans step 1 n a b
        (some ((absorbingNext step)^[n] b)) first (ih b)
      simpa only [Function.iterate_succ_apply, absorbingNext_of_some step hs] using full

theorem absorbing_eq_of_execution (step : C → Option C) {a b : C} {T : Nat}
    (execution : StateTransition.EvalsToInTime step a (some b) T)
    (halted : step b = none) : (absorbingNext step)^[T] a = b := by
  have hs : (absorbingNext step)^[execution.steps] a = b := by
    apply absorbing_of_successfulTrace
    exact execution.evals_in_steps
  have ht : T = (T - execution.steps) + execution.steps :=
    (Nat.sub_add_cancel execution.steps_le_m).symm
  rw [ht, Function.iterate_add_apply, hs]
  exact Function.iterate_fixed (absorbingNext_of_none step halted) _

end Transition

abbrev stickyNext (tm : Turing.FinTM2) : tm.Cfg → tm.Cfg := absorbingNext tm.step

def run (tm : Turing.FinTM2) (input : List (tm.Γ tm.k₀)) (n : Nat) : tm.Cfg :=
  (stickyNext tm)^[n] (Turing.initList tm input)

@[simp] theorem run_zero (tm : Turing.FinTM2) (input : List (tm.Γ tm.k₀)) :
    run tm input 0 = Turing.initList tm input := rfl

theorem run_succ (tm : Turing.FinTM2) (input : List (tm.Γ tm.k₀)) (n : Nat) :
    run tm input (n + 1) = stickyNext tm (run tm input n) := by
  simp only [run, Function.iterate_succ_apply']

theorem step_none_iff (tm : Turing.FinTM2) (c : tm.Cfg) :
    tm.step c = none ↔ c.l = none := by
  cases c with
  | mk label state tapes =>
    cases label <;> simp [Turing.FinTM2.step, Turing.TM2.step]
    rfl

theorem stickyNext_live (tm : Turing.FinTM2) (c : tm.Cfg) (label : tm.Λ)
    (h : c.l = some label) :
    stickyNext tm c = Turing.TM2.stepAux (tm.m label) c.var c.stk := by
  cases c with
  | mk l state tapes =>
    change l = some label at h
    subst l
    rfl

theorem run_eq_halt_of_outputs (tm : Turing.FinTM2)
    (input : List (tm.Γ tm.k₀)) (output : List (tm.Γ tm.k₁)) (T : Nat)
    (h : Turing.TM2OutputsInTime tm input (some output) T) :
    run tm input T = Turing.haltList tm output :=
  absorbing_eq_of_execution tm.step h rfl

def outputs_of_run_eq_halt (tm : Turing.FinTM2)
    (input : List (tm.Γ tm.k₀)) (output : List (tm.Γ tm.k₁)) (T : Nat)
    (h : run tm input T = Turing.haltList tm output) :
    Turing.TM2OutputsInTime tm input (some output) T := by
  change StateTransition.EvalsToInTime tm.step (Turing.initList tm input)
    (some (Turing.haltList tm output)) T
  have e : StateTransition.EvalsToInTime tm.step (Turing.initList tm input)
      (some (run tm input T)) T := executionToAbsorbing tm.step _ T
  rw [h] at e
  exact e

theorem outputs_iff_run_eq_halt (tm : Turing.FinTM2)
    (input : List (tm.Γ tm.k₀)) (output : List (tm.Γ tm.k₁)) (T : Nat) :
    Nonempty (Turing.TM2OutputsInTime tm input (some output) T) ↔
      run tm input T = Turing.haltList tm output :=
  ⟨fun ⟨h⟩ => run_eq_halt_of_outputs tm input output T h,
    fun h => ⟨outputs_of_run_eq_halt tm input output T h⟩⟩

def IsStickyTrace (tm : Turing.FinTM2) (T : Nat) (tr : Fin (T + 1) → tm.Cfg) : Prop :=
  ∀ i : Fin T, tr i.succ = stickyNext tm (tr i.castSucc)

def boundedTrace (tm : Turing.FinTM2) (input : List (tm.Γ tm.k₀)) (T : Nat) :
    Fin (T + 1) → tm.Cfg := fun i => run tm input i.val

theorem boundedTrace_isSticky (tm : Turing.FinTM2)
    (input : List (tm.Γ tm.k₀)) (T : Nat) : IsStickyTrace tm T (boundedTrace tm input T) := by
  intro i
  exact run_succ tm input i.val

theorem trace_eq_run (tm : Turing.FinTM2) (input : List (tm.Γ tm.k₀)) (T : Nat)
    (tr : Fin (T + 1) → tm.Cfg) (initial : tr 0 = Turing.initList tm input)
    (next : IsStickyTrace tm T tr) (i : Fin (T + 1)) : tr i = run tm input i.val := by
  have h : ∀ n (hn : n ≤ T), tr ⟨n, by omega⟩ = run tm input n := by
    intro n
    induction n with
    | zero => intro hn; exact initial
    | succ n ih =>
      intro hn
      have hnT : n < T := by omega
      have hs := next ⟨n, hnT⟩
      change tr ⟨n + 1, by omega⟩ = stickyNext tm (tr ⟨n, by omega⟩) at hs
      rw [run_succ, ← ih (Nat.le_of_lt hnT)]
      exact hs
  exact h i.val (by omega)

theorem outputs_iff_trace (tm : Turing.FinTM2)
    (input : List (tm.Γ tm.k₀)) (output : List (tm.Γ tm.k₁)) (T : Nat) :
    Nonempty (Turing.TM2OutputsInTime tm input (some output) T) ↔
      ∃ tr : Fin (T + 1) → tm.Cfg,
        tr 0 = Turing.initList tm input ∧ IsStickyTrace tm T tr ∧
        tr (Fin.last T) = Turing.haltList tm output := by
  constructor
  · rintro ⟨h⟩
    refine ⟨boundedTrace tm input T, rfl, boundedTrace_isSticky tm input T, ?_⟩
    exact run_eq_halt_of_outputs tm input output T h
  · rintro ⟨tr, h0, hs, hT⟩
    apply (outputs_iff_run_eq_halt tm input output T).mpr
    have he := trace_eq_run tm input T tr h0 hs (Fin.last T)
    exact he.symm.trans hT

noncomputable def stackCapacity (tm : Turing.FinTM2)
    (input : List (tm.Γ tm.k₀)) (T : Nat) : Nat :=
  input.length + T * Runtime.programPushBound tm

theorem run_stack_bound (tm : Turing.FinTM2) (input : List (tm.Γ tm.k₀))
    (n : Nat) (k : tm.K) :
    ((run tm input n).stk k).length ≤ input.length + n * Runtime.programPushBound tm := by
  have h := Runtime.executionSizeBound tm.step (fun c => (c.stk k).length)
    (Runtime.programPushBound tm) (Runtime.stepStackLength tm k)
    (executionToAbsorbing tm.step (Turing.initList tm input) n)
  exact h.trans (Nat.add_le_add_right (Runtime.initialStackLength tm input k) _)

theorem run_stack_le (tm : Turing.FinTM2) (input : List (tm.Γ tm.k₀))
    (T n : Nat) (hn : n ≤ T) (k : tm.K) :
    ((run tm input n).stk k).length ≤ stackCapacity tm input T :=
  (run_stack_bound tm input n k).trans
    (Nat.add_le_add_left (Nat.mul_le_mul_right (Runtime.programPushBound tm) hn) _)

theorem statement_budget (tm : Turing.FinTM2) (input : List (tm.Γ tm.k₀))
    (T n : Nat) (hn : n < T) (label : tm.Λ) (k : tm.K) :
    ((run tm input n).stk k).length + Runtime.statementPushBound (tm.m label) ≤
      stackCapacity tm input T := by
  have hlen := run_stack_bound tm input n k
  have hstmt := Runtime.statement_le_programPushBound tm label
  have htime := Nat.mul_le_mul_right (Runtime.programPushBound tm) (show n + 1 ≤ T by omega)
  rw [Nat.add_mul, Nat.one_mul] at htime
  unfold stackCapacity
  omega

section Statement
variable {K : Type} {Γ : K → Type} {Λ σ : Type} [DecidableEq K]

def StackBound (S : Nat) (tapes : ∀ k, List (Γ k)) : Prop :=
  ∀ k, (tapes k).length ≤ S

def StatementSafe (S : Nat) : Turing.TM2.Stmt Γ Λ σ → σ → (∀ k, List (Γ k)) → Prop
  | .push k f q, v, tapes => StackBound S tapes ∧ (tapes k).length < S ∧
      StatementSafe S q v (Function.update tapes k (f v :: tapes k))
  | .peek k f q, v, tapes => StackBound S tapes ∧
      StatementSafe S q (f v (tapes k).head?) tapes
  | .pop k f q, v, tapes => StackBound S tapes ∧
      StatementSafe S q (f v (tapes k).head?) (Function.update tapes k (tapes k).tail)
  | .load f q, v, tapes => StackBound S tapes ∧ StatementSafe S q (f v) tapes
  | .branch f yes no, v, tapes => StackBound S tapes ∧
      (if f v then StatementSafe S yes v tapes else StatementSafe S no v tapes)
  | .goto _, _, tapes => StackBound S tapes
  | .halt, _, tapes => StackBound S tapes

theorem StatementSafe.stackBound {S : Nat} {stmt : Turing.TM2.Stmt Γ Λ σ}
    {state : σ} {tapes : ∀ k, List (Γ k)} (h : StatementSafe S stmt state tapes) :
    StackBound S tapes := by
  cases stmt <;> first | exact h.1 | exact h

theorem StatementSafe.push_room {S : Nat} {k : K} {f : σ → Γ k}
    {q : Turing.TM2.Stmt Γ Λ σ} {state : σ} {tapes : ∀ k, List (Γ k)}
    (h : StatementSafe S (.push k f q) state tapes) : (tapes k).length < S := h.2.1

theorem StatementSafe.mono {S S' : Nat} {stmt : Turing.TM2.Stmt Γ Λ σ}
    {state : σ} {tapes : ∀ k, List (Γ k)} (h : StatementSafe S stmt state tapes)
    (hSS' : S ≤ S') : StatementSafe S' stmt state tapes := by
  induction stmt generalizing state tapes with
  | push j f q ih =>
    exact ⟨fun k => (h.1 k).trans hSS', lt_of_lt_of_le h.2.1 hSS', ih h.2.2⟩
  | peek j f q ih => exact ⟨fun k => (h.1 k).trans hSS', ih h.2⟩
  | pop j f q ih => exact ⟨fun k => (h.1 k).trans hSS', ih h.2⟩
  | load f q ih => exact ⟨fun k => (h.1 k).trans hSS', ih h.2⟩
  | branch f yes no ihYes ihNo =>
    refine ⟨fun k => (h.1 k).trans hSS', ?_⟩
    cases decision : f state with
    | false =>
      have hs : StatementSafe S no state tapes := by simpa [decision] using h.2
      simpa [decision] using ihNo hs
    | true =>
      have hs : StatementSafe S yes state tapes := by simpa [decision] using h.2
      simpa [decision] using ihYes hs
  | goto f => exact fun k => (h k).trans hSS'
  | halt => exact fun k => (h k).trans hSS'

theorem StatementSafe.resultBound {S : Nat} {stmt : Turing.TM2.Stmt Γ Λ σ}
    {state : σ} {tapes : ∀ k, List (Γ k)} (h : StatementSafe S stmt state tapes) :
    StackBound S (Turing.TM2.stepAux stmt state tapes).stk := by
  induction stmt generalizing state tapes with
  | push j f q ih => exact ih h.2.2
  | peek j f q ih => exact ih h.2
  | pop j f q ih => exact ih h.2
  | load f q ih => exact ih h.2
  | branch f yes no ihYes ihNo =>
    cases decision : f state with
    | false =>
      have hs : StatementSafe S no state tapes := by simpa [decision] using h.2
      simpa only [Turing.TM2.stepAux, decision, Bool.cond_false] using ihNo hs
    | true =>
      have hs : StatementSafe S yes state tapes := by simpa [decision] using h.2
      simpa only [Turing.TM2.stepAux, decision, Bool.cond_true] using ihYes hs
  | goto f => exact h
  | halt => exact h

omit [DecidableEq K] in
private theorem stackBound_of_budget (S : Nat) (stmt : Turing.TM2.Stmt Γ Λ σ)
    (tapes : ∀ k, List (Γ k))
    (h : ∀ k, (tapes k).length + Runtime.statementPushBound stmt ≤ S) : StackBound S tapes := by
  intro k
  have hk := h k
  omega

theorem statementSafe_of_budget (S : Nat) (stmt : Turing.TM2.Stmt Γ Λ σ)
    (state : σ) (tapes : ∀ k, List (Γ k))
    (h : ∀ k, (tapes k).length + Runtime.statementPushBound stmt ≤ S) :
    StatementSafe S stmt state tapes := by
  induction stmt generalizing state tapes with
  | push j f q ih =>
    refine ⟨stackBound_of_budget S _ tapes h, ?_, ?_⟩
    · have hj := h j
      simp only [Runtime.statementPushBound] at hj
      omega
    · apply ih
      intro k
      have hk := h k
      have changed : ((Function.update tapes j (f state :: tapes j)) k).length ≤
          (tapes k).length + 1 := by
        by_cases same : k = j
        · subst k; simp
        · simp [Function.update, same]
      simp only [Runtime.statementPushBound] at hk
      omega
  | peek j f q ih =>
    exact ⟨stackBound_of_budget S _ tapes h, ih _ _ h⟩
  | pop j f q ih =>
    refine ⟨stackBound_of_budget S _ tapes h, ?_⟩
    apply ih
    intro k
    have hk := h k
    have changed : ((Function.update tapes j (tapes j).tail) k).length ≤
        (tapes k).length := by
      by_cases same : k = j
      · subst k; simp
      · simp [Function.update, same]
    simp only [Runtime.statementPushBound] at hk
    omega
  | load f q ih =>
    exact ⟨stackBound_of_budget S _ tapes h, ih _ _ h⟩
  | branch f yes no ihYes ihNo =>
    refine ⟨stackBound_of_budget S _ tapes h, ?_⟩
    cases decision : f state with
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      apply ihNo
      intro k
      have hk := h k
      have hm := Nat.le_max_right (Runtime.statementPushBound yes) (Runtime.statementPushBound no)
      simp only [Runtime.statementPushBound] at hk
      omega
    | true =>
      simp only [↓reduceIte]
      apply ihYes
      intro k
      have hk := h k
      have hm := Nat.le_max_left (Runtime.statementPushBound yes) (Runtime.statementPushBound no)
      simp only [Runtime.statementPushBound] at hk
      omega
  | goto f => exact stackBound_of_budget S _ tapes h
  | halt => exact stackBound_of_budget S _ tapes h

end Statement

theorem run_statement_safe (tm : Turing.FinTM2) (input : List (tm.Γ tm.k₀))
    (T n : Nat) (hn : n < T) (label : tm.Λ) :
    StatementSafe (stackCapacity tm input T) (tm.m label)
      (run tm input n).var (run tm input n).stk :=
  statementSafe_of_budget _ _ _ _ (statement_budget tm input T n hn label)

theorem trace_stack_le (tm : Turing.FinTM2) (input : List (tm.Γ tm.k₀)) (T : Nat)
    (tr : Fin (T + 1) → tm.Cfg) (initial : tr 0 = Turing.initList tm input)
    (next : IsStickyTrace tm T tr) (i : Fin (T + 1)) (k : tm.K) :
    ((tr i).stk k).length ≤ stackCapacity tm input T := by
  rw [trace_eq_run tm input T tr initial next i]
  exact run_stack_le tm input T i.val (by omega) k

theorem trace_statement_safe (tm : Turing.FinTM2) (input : List (tm.Γ tm.k₀)) (T : Nat)
    (tr : Fin (T + 1) → tm.Cfg) (initial : tr 0 = Turing.initList tm input)
    (next : IsStickyTrace tm T tr) (i : Fin T) (label : tm.Λ) :
    StatementSafe (stackCapacity tm input T) (tm.m label)
      (tr i.castSucc).var (tr i.castSucc).stk := by
  rw [trace_eq_run tm input T tr initial next i.castSucc]
  exact run_statement_safe tm input T i.val i.isLt label

end BinPackingGames.Foundations.Complexity.CookLevin.BoundedExecution

end OAI
