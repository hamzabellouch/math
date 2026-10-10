import Mathlib
import OAI.Combinatorics.IndependentSets.PCP.RawInitialTables
import OAI.Combinatorics.IndependentSets.Encoding.GraphTableComplexity

namespace OAI

namespace IndependentSetsGames.Foundations.PCP.RawInitialMachineBudget

open Target Complexity

def nameSum {n : Nat} (c : Clause n) : Nat :=
  (c)[0].variableIndex.val + (c)[1].variableIndex.val + (c)[2].variableIndex.val

def bodyTime {n : Nat} (i : Nat) (c : Clause n) : Nat :=
  6 * n + 18 * i + 2 * nameSum c +
    2 * (encodeWords (Complexity.clauseWords c)).length + 63

def loopTime {n : Nat} (i : Nat) : List (Clause n) → Nat
  | [] => 1
  | c :: cs => bodyTime i c + loopTime (i + 1) cs

theorem nameSum_le {n : Nat} (c : Clause n) : nameSum c ≤ 3 * n := by
  have h0 := (c)[0].variableIndex.isLt
  have h1 := (c)[1].variableIndex.isLt
  have h2 := (c)[2].variableIndex.isLt
  unfold nameSum
  omega

theorem bodyTime_le {n : Nat} (i : Nat) (c : Clause n) :
    bodyTime i c ≤ 18 * n + 18 * i + 81 := by
  have hn := nameSum_le c
  have hb := clauseBits_length_le c
  unfold bodyTime
  omega

theorem loopTime_le {n : Nat} (i : Nat) (cs : List (Clause n)) :
    loopTime i cs ≤ cs.length * (18 * n + 18 * (i + cs.length) + 81) + 1 := by
  induction cs generalizing i with
  | nil => simp [loopTime]
  | cons c cs ih =>
      have hc := bodyTime_le i c
      have ht := ih (i + 1)
      have hbound : bodyTime i c ≤ 18 * n + 18 * (i + (c :: cs).length) + 81 := by
        simp only [List.length_cons]
        omega
      have hsame : 18 * n + 18 * (i + 1 + cs.length) + 81 =
          18 * n + 18 * (i + (c :: cs).length) + 81 := by
        simp only [List.length_cons]
        omega
      rw [hsame] at ht
      rw [loopTime]
      calc
        _ ≤ (18 * n + 18 * (i + (c :: cs).length) + 81) +
            (cs.length * (18 * n + 18 * (i + (c :: cs).length) + 81) + 1) :=
          Nat.add_le_add hbound ht
        _ = _ := by rw [List.length_cons]; ring

theorem input_header_bound (F : Formula) :
    F.«variables» + F.clauses.length + 2 ≤ (formulaBits F).length := by
  simp only [formulaBits, formulaWords, encodeWords_append, List.length_append,
    encodeWords, encodeWord_length, List.length_nil]
  omega

theorem graph_size_bound (F : Formula) :
    (RawInitialTables.table F).vertices + (RawInitialTables.table F).darts ≤
      7 * (formulaBits F).length := by
  rw [RawInitialTables.initial_size]
  have h := input_header_bound F
  omega

def fullBudget (F : Formula) : Nat :=
  6 * F.«variables» + 10 * F.clauses.length + 30 + loopTime 0 F.clauses +
    (GraphTables.tableBits (RawInitialTables.table F)).length

noncomputable def timePolynomial : Polynomial Nat :=
  Polynomial.C 100 * Polynomial.X ^ 2 + Polynomial.C 60000 * Polynomial.X +
    Polynomial.C 100

theorem timePolynomial_eval (N : Nat) :
    timePolynomial.eval N = 100 * N ^ 2 + 60000 * N + 100 := by
  simp [timePolynomial]

theorem fullBudget_le (F : Formula) :
    fullBudget F ≤ timePolynomial.eval (formulaBits F).length := by
  have hinput := input_header_bound F
  have hloop := loopTime_le 0 F.clauses
  have hout := GraphTableComplexity.bits_le_of_size_le (RawInitialTables.table F)
    (graph_size_bound F)
  rw [GraphTableComplexity.encodingPolynomial_eval] at hout
  simp only [Nat.zero_add] at hloop
  have hm : F.clauses.length ≤ (formulaBits F).length := by omega
  have hcoefficient : 18 * F.«variables» + 18 * F.clauses.length + 81 ≤
      18 * (formulaBits F).length + 81 := by omega
  have hproduct := Nat.mul_le_mul hm hcoefficient
  rw [timePolynomial_eval]
  unfold fullBudget
  nlinarith

end IndependentSetsGames.Foundations.PCP.RawInitialMachineBudget
namespace IndependentSetsGames.Foundations.Complexity.Runtime

def statementPushBound {K : Type} {Γ : K → Type} {Λ σ : Type} :
    Turing.TM2.Stmt Γ Λ σ → Nat
  | .push _ _ next => statementPushBound next + 1
  | .peek _ _ next => statementPushBound next
  | .pop _ _ next => statementPushBound next
  | .load _ next => statementPushBound next
  | .branch _ yes no => max (statementPushBound yes) (statementPushBound no)
  | .goto _ => 0
  | .halt => 0

def maxLabelPushes {K : Type} {Γ : K → Type} {Λ σ : Type}
    (program : Λ → Turing.TM2.Stmt Γ Λ σ) : List Λ → Nat
  | [] => 0
  | label :: rest => max (statementPushBound (program label)) (maxLabelPushes program rest)

theorem maxLabelPushes_ge {K : Type} {Γ : K → Type} {Λ σ : Type}
    (program : Λ → Turing.TM2.Stmt Γ Λ σ) (labels : List Λ) (label : Λ)
    (member : label ∈ labels) :
    statementPushBound (program label) ≤ maxLabelPushes program labels := by
  induction labels with
  | nil => simp at member
  | cons first rest ih =>
      simp only [List.mem_cons] at member
      rcases member with rfl | member
      · exact Nat.le_max_left _ _
      · exact Nat.le_trans (ih member) (Nat.le_max_right _ _)

noncomputable def programPushBound (tm : Turing.FinTM2) : Nat :=
  maxLabelPushes tm.m tm.ΛFin.elems.toList

theorem statement_le_programPushBound (tm : Turing.FinTM2) (label : tm.Λ) :
    statementPushBound (tm.m label) ≤ programPushBound tm := by
  apply maxLabelPushes_ge
  simpa using tm.ΛFin.complete label

theorem stepAuxStackLength {K : Type} {Γ : K → Type} {Λ σ : Type} [DecidableEq K]
    (stmt : Turing.TM2.Stmt Γ Λ σ) (state : σ) (tapes : ∀ k, List (Γ k)) (k : K) :
    ((Turing.TM2.stepAux stmt state tapes).stk k).length ≤
      (tapes k).length + statementPushBound stmt := by
  induction stmt generalizing state tapes with
  | push j f next ih =>
      have changed : ((Function.update tapes j (f state :: tapes j)) k).length ≤
          (tapes k).length + 1 := by
        by_cases same : k = j
        · subst k; simp
        · simp [Function.update, same]
      have h := ih state (Function.update tapes j (f state :: tapes j))
      simp only [Turing.TM2.stepAux, statementPushBound]
      omega
  | peek j f next ih =>
      simpa only [Turing.TM2.stepAux, statementPushBound] using
        ih (f state (tapes j).head?) tapes
  | pop j f next ih =>
      have changed : ((Function.update tapes j (tapes j).tail) k).length ≤
          (tapes k).length := by
        by_cases same : k = j
        · subst k; simp
        · simp [Function.update, same]
      have h := ih (f state (tapes j).head?) (Function.update tapes j (tapes j).tail)
      simp only [Turing.TM2.stepAux, statementPushBound]
      omega
  | load f next ih =>
      simpa only [Turing.TM2.stepAux, statementPushBound] using ih (f state) tapes
  | branch condition yes no ihYes ihNo =>
      cases decision : condition state with
      | false =>
          have h := ihNo state tapes
          have hm := Nat.le_max_right (statementPushBound yes) (statementPushBound no)
          simp only [Turing.TM2.stepAux, statementPushBound, decision, Bool.cond_false]
          omega
      | true =>
          have h := ihYes state tapes
          have hm := Nat.le_max_left (statementPushBound yes) (statementPushBound no)
          simp only [Turing.TM2.stepAux, statementPushBound, decision, Bool.cond_true]
          omega
  | goto f => simp [Turing.TM2.stepAux, statementPushBound]
  | halt => simp [Turing.TM2.stepAux, statementPushBound]

private theorem iterateSizeBound {α : Type} (f : α → α) (size : α → Nat) (C : Nat)
    (oneStep : ∀ x, size (f x) ≤ size x + C) (n : Nat) (x : α) :
    size ((f^[n]) x) ≤ size x + n * C := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hs := oneStep ((f^[n]) x)
      have bound : size (f ((f^[n]) x)) ≤ size x + (n + 1) * C := by
        rw [Nat.add_mul, Nat.one_mul]
        omega
      simpa only [Function.iterate_succ_apply'] using bound

theorem executionSizeBound {σ : Type} (step : σ → Option σ) (size : σ → Nat) (C : Nat)
    (oneStep : ∀ a b, step a = some b → size b ≤ size a + C)
    {start finish : σ} {budget : Nat}
    (execution : StateTransition.EvalsToInTime step start (some finish) budget) :
    size finish ≤ size start + budget * C := by
  let liftedSize : Option σ → Nat := fun state => (state.map size).getD 0
  have liftedStep : ∀ state : Option σ,
      liftedSize (state.bind step) ≤ liftedSize state + C := by
    intro state
    cases state with
    | none => simp [liftedSize]
    | some a =>
        cases transition : step a with
        | none => simp [liftedSize, transition]
        | some b => simpa [liftedSize, transition] using oneStep a b transition
  have bound := iterateSizeBound (fun state : Option σ => state.bind step)
    liftedSize C liftedStep execution.steps (some start)
  change liftedSize ((flip bind step)^[execution.steps] (some start)) ≤ _ at bound
  rw [execution.evals_in_steps] at bound
  simp only [liftedSize, Option.map_some, Option.getD_some] at bound
  exact Nat.le_trans bound (Nat.add_le_add_left
    (Nat.mul_le_mul_right C execution.steps_le_m) _)

theorem stepStackLength (tm : Turing.FinTM2) (k : tm.K) (a b : tm.Cfg)
    (transition : tm.step a = some b) :
    (b.stk k).length ≤ (a.stk k).length + programPushBound tm := by
  cases a with
  | mk label state tapes =>
      cases label with
      | none => simp [Turing.FinTM2.step, Turing.TM2.step] at transition
      | some label =>
          have result := Option.some.inj transition
          rw [← result]
          exact Nat.le_trans (stepAuxStackLength _ _ _ _)
            (Nat.add_le_add_left (statement_le_programPushBound tm label) _)

theorem initialStackLength (tm : Turing.FinTM2) (input : List (tm.Γ tm.k₀)) (k : tm.K) :
    ((Turing.initList tm input).stk k).length ≤ input.length := by
  simp only [Turing.initList]
  split
  next same => subst k; exact Nat.le_refl _
  next _ => simp

@[simp] theorem haltedOutputLength (tm : Turing.FinTM2) (output : List (tm.Γ tm.k₁)) :
    ((Turing.haltList tm output).stk tm.k₁).length = output.length := by
  simp [Turing.haltList]

theorem outputLength_le (tm : Turing.FinTM2) (input : List (tm.Γ tm.k₀))
    (output : List (tm.Γ tm.k₁)) (budget : Nat)
    (execution : Turing.TM2OutputsInTime tm input (some output) budget) :
    output.length ≤ input.length + budget * programPushBound tm := by
  have bound := executionSizeBound tm.step (fun cfg => (cfg.stk tm.k₁).length)
    (programPushBound tm) (stepStackLength tm tm.k₁) execution
  calc
    output.length = ((Turing.haltList tm output).stk tm.k₁).length := (haltedOutputLength tm output).symm
    _ ≤ ((Turing.initList tm input).stk tm.k₁).length + budget * programPushBound tm := bound
    _ ≤ input.length + budget * programPushBound tm :=
      Nat.add_le_add_right (initialStackLength tm input tm.k₁) _

theorem encodedOutputLength {α β αΓ βΓ : Type}
    {ea : α → List αΓ} {eb : β → List βΓ} {f : α → β}
    (certificate : Turing.TM2ComputableInPolyTime ea eb f) (a : α) :
    (eb (f a)).length ≤
      (Polynomial.X + Polynomial.C (programPushBound certificate.tm) * certificate.time).eval
        (ea a).length := by
  have bound := outputLength_le certificate.tm _ _ _ (certificate.outputsFun a)
  simpa only [List.length_map, Polynomial.eval_add, Polynomial.eval_X,
    Polynomial.eval_mul, Polynomial.eval_C, Nat.mul_comm] using bound

end IndependentSetsGames.Foundations.Complexity.Runtime

end OAI
