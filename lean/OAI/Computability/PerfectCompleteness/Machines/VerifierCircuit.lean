import OAI.Computability.PerfectCompleteness.Machines.CircuitBatchLemmas
import OAI.Computability.PerfectCompleteness.Machines.MachineCircuit
import OAI.Computability.PerfectCompleteness.Machines.WitnessCircuit
import OAI.Computability.PerfectCompleteness.Machines.WitnessEncodingLemmas

namespace OAI

section

noncomputable section
namespace UniqueGamesTheorem.Foundations.Complexity.CookLevin.VerifierCircuit

open Turing StatementCircuit CircuitBatch
open scoped BigOperators

local instance alphabetFinite (V : NPVerifier) : ∀ k, Fintype (V.computation.tm.Γ k) :=
  V.finiteAlphabet
local instance labelFinite (V : NPVerifier) : Fintype V.computation.tm.Λ :=
  V.computation.tm.ΛFin
local instance stateFinite (V : NPVerifier) : Fintype V.computation.tm.σ :=
  V.computation.tm.σFin
local instance labelDecidable (V : NPVerifier) : DecidableEq V.computation.tm.Λ :=
  Classical.decEq _
local instance stateDecidable (V : NPVerifier) : DecidableEq V.computation.tm.σ :=
  Classical.decEq _
local instance alphabetDecidable (V : NPVerifier) : ∀ k, DecidableEq (V.computation.tm.Γ k) :=
  fun _ => Classical.decEq _

def capacity (V : NPVerifier) (n : Nat) : Nat :=
  2 * n + V.witnessBound.eval n + 1 + V.horizon n * Runtime.programPushBound V.computation.tm

theorem capacity_pos (V : NPVerifier) (n : Nat) : 1 ≤ capacity V n := by
  unfold capacity
  omega

abbrev FreeBits (V : NPVerifier) (input : List Bool) :=
  WitnessEncoding.Bits (V.witnessBound.eval input.length)

def machineInput (V : NPVerifier) (input : List Bool) (bits : FreeBits V input) :=
  (pairBits (input, WitnessEncoding.decode bits)).map V.computation.inputAlphabet.invFun

def actualRun (V : NPVerifier) (input : List Bool) (bits : FreeBits V input) (t : Nat) :
    V.computation.tm.Cfg := BoundedExecution.run V.computation.tm (machineInput V input bits) t

def accepting (V : NPVerifier) : V.computation.tm.Cfg :=
  haltList V.computation.tm ([true].map V.computation.outputAlphabet.invFun)

theorem stackCapacity_le (V : NPVerifier) (input : List Bool) (bits : FreeBits V input) :
    BoundedExecution.stackCapacity V.computation.tm (machineInput V input bits)
      (V.horizon input.length) ≤ capacity V input.length := by
  have h := WitnessEncoding.pairBits_decode_length_le input bits
  simp only [BoundedExecution.stackCapacity, machineInput, List.length_map, capacity]
  omega

theorem actualRun_stack_le (V : NPVerifier) (input : List Bool) (bits : FreeBits V input)
    (t : Nat) (ht : t ≤ V.horizon input.length) (k : V.computation.tm.K) :
    ((actualRun V input bits t).stk k).length ≤ capacity V input.length :=
  (BoundedExecution.run_stack_le V.computation.tm (machineInput V input bits)
    (V.horizon input.length) t ht k).trans (stackCapacity_le V input bits)

theorem actualRun_stepSafe (V : NPVerifier) (input : List Bool) (bits : FreeBits V input)
    (t : Nat) (ht : t < V.horizon input.length) :
    MachineCircuit.StepSafe (capacity V input.length) V.computation.tm.m
      (actualRun V input bits t) := by
  intro label _
  apply BoundedExecution.statementSafe_of_budget
  intro k
  exact (BoundedExecution.statement_budget V.computation.tm (machineInput V input bits)
    (V.horizon input.length) t ht label k).trans (stackCapacity_le V input bits)

theorem accepting_stack_le (V : NPVerifier) (input : List Bool) (k : V.computation.tm.K) :
    ((accepting V).stk k).length ≤ capacity V input.length := by
  by_cases hk : k = V.computation.tm.k₁
  · subst k
    simpa [accepting, haltList] using capacity_pos V input.length
  · simp [accepting, haltList, hk]

theorem actualRun_accepting_iff (V : NPVerifier) (input : List Bool) (bits : FreeBits V input) :
    actualRun V input bits (V.horizon input.length) = accepting V ↔
      V.verify (input, WitnessEncoding.decode bits) = true := by
  have hr := BoundedExecution.run_eq_halt_of_outputs V.computation.tm
    (machineInput V input bits)
    ([V.verify (input, WitnessEncoding.decode bits)].map V.computation.outputAlphabet.invFun)
    (V.horizon input.length)
    (V.runWithinHorizon input (WitnessEncoding.decode bits) (WitnessEncoding.decode_length_le bits))
  change actualRun V input bits (V.horizon input.length) = _ at hr
  rw [hr]
  constructor
  · intro h
    have hs := congrArg (fun c : V.computation.tm.Cfg => c.stk V.computation.tm.k₁) h
    have he : V.computation.outputAlphabet.invFun (V.verify (input, WitnessEncoding.decode bits)) =
        V.computation.outputAlphabet.invFun true := by
      simpa [accepting, haltList] using hs
    exact V.computation.outputAlphabet.symm.injective he
  · intro h
    simp [h, accepting]

abbrev Bit (V : NPVerifier) (input : List Bool) :=
  ConfigBit V.computation.tm.Γ V.computation.tm.Λ V.computation.tm.σ (capacity V input.length)

def indexing (V : NPVerifier) :
    ConfigIndex.Indexing V.computation.tm.Γ V.computation.tm.Λ V.computation.tm.σ :=
  ConfigIndex.ofMachine V.computation.tm

abbrev width (V : NPVerifier) (input : List Bool) : Nat :=
  (indexing V).width (capacity V input.length)

def bitEquiv (V : NPVerifier) (input : List Bool) : Bit V input ≃ Fin (width V input) :=
  (indexing V).configIndexEquiv (capacity V input.length)

def bitWire (V : NPVerifier) (input : List Bool) (b : Bit V input) : Fin (width V input + 1) :=
  (bitEquiv V input b).castSucc

def stateEncoding (V : NPVerifier) (input : List Bool) (cfg : V.computation.tm.Cfg)
    (valid : Bool) : Fin (width V input + 1) → Bool :=
  Fin.lastCases valid (fun j => configEncoding (capacity V input.length) cfg
    ((bitEquiv V input).symm j))

@[simp] theorem stateEncoding_last (V : NPVerifier) (input : List Bool)
    (cfg : V.computation.tm.Cfg) (valid : Bool) :
    stateEncoding V input cfg valid (Fin.last (width V input)) = valid := by
  simp [stateEncoding]

@[simp] theorem stateEncoding_bitWire (V : NPVerifier) (input : List Bool)
    (cfg : V.computation.tm.Cfg) (valid : Bool) (b : Bit V input) :
    stateEncoding V input cfg valid (bitWire V input b) =
      configEncoding (capacity V input.length) cfg b := by
  simp [stateEncoding, bitWire]

def initialExpressions (V : NPVerifier) (input : List Bool) :
    Fin (width V input + 1) → Expr (Fin (2 * V.witnessBound.eval input.length + 1)) :=
  Fin.lastCases (WitnessCircuit.validityExpr (V.witnessBound.eval input.length))
    (fun j => WitnessCircuit.initExpr V input (capacity V input.length)
      ((bitEquiv V input).symm j))

def stepExpressions (V : NPVerifier) (input : List Bool) :
    Fin (width V input + 1) → Expr (Fin (width V input + 1)) :=
  Fin.lastCases (.input (Fin.last (width V input)))
    (fun j => (MachineCircuit.stickyExpr (capacity V input.length) V.computation.tm.m
      ((bitEquiv V input).symm j)).rename (bitWire V input))

theorem initialExpressions_eval (V : NPVerifier) (input : List Bool) (bits : FreeBits V input)
    (hv : WitnessEncoding.Valid bits) :
    (fun j => (initialExpressions V input j).eval bits) =
      stateEncoding V input (WitnessEncoding.initial V input bits)
        ((WitnessCircuit.validityExpr _).eval bits) := by
  funext j
  refine Fin.lastCases ?_ (fun i => ?_) j
  · simp [initialExpressions, stateEncoding]
  · simpa [initialExpressions, stateEncoding] using
      WitnessCircuit.eval_initExpr V input (capacity V input.length) bits hv
        ((bitEquiv V input).symm i)

theorem stepExpressions_eval (V : NPVerifier) (input : List Bool) (cfg : V.computation.tm.Cfg)
    (safe : MachineCircuit.StepSafe (capacity V input.length) V.computation.tm.m cfg)
    (valid : Bool) :
    Frame.network (stepExpressions V input) (stateEncoding V input cfg valid) =
      stateEncoding V input (BoundedExecution.stickyNext V.computation.tm cfg) valid := by
  funext j
  refine Fin.lastCases ?_ (fun i => ?_) j
  · simp [Frame.network, stepExpressions, Expr.eval, stateEncoding]
  · simp only [Frame.network, stepExpressions, Fin.lastCases_castSucc, Expr.eval_rename]
    have he : (fun b => stateEncoding V input cfg valid (bitWire V input b)) =
        configEncoding (capacity V input.length) cfg := by funext b; simp
    rw [he, MachineCircuit.stickyExpr_eval _ _ cfg safe]
    simp only [stateEncoding, Fin.lastCases_castSucc]
    rfl

def initialFrame (V : NPVerifier) (input : List Bool) :
    Frame (2 * V.witnessBound.eval input.length + 1) (width V input + 1) :=
  (Frame.initial id).step (initialExpressions V input)

def timeFrame (V : NPVerifier) (input : List Bool) (t : Nat) :
    Frame (2 * V.witnessBound.eval input.length + 1) (width V input + 1) :=
  (initialFrame V input).repeat (stepExpressions V input) t

theorem initialFrame_eval (V : NPVerifier) (input : List Bool) (bits : FreeBits V input)
    (hv : WitnessEncoding.Valid bits) :
    (initialFrame V input).eval bits = stateEncoding V input
      (WitnessEncoding.initial V input bits) ((WitnessCircuit.validityExpr _).eval bits) := by
  rw [initialFrame, Frame.step_eval_fun]
  have hi : (Frame.initial id).eval bits = bits := by funext i; simp
  rw [hi]
  exact initialExpressions_eval V input bits hv

theorem timeFrame_validity (V : NPVerifier) (input : List Bool) (bits : FreeBits V input)
    (t : Nat) :
    (timeFrame V input t).eval bits (Fin.last (width V input)) =
      (WitnessCircuit.validityExpr (V.witnessBound.eval input.length)).eval bits := by
  induction t with
  | zero =>
    simp only [timeFrame, Frame.repeat, initialFrame, Frame.step_eval,
      initialExpressions, Fin.lastCases_last]
    apply Expr.eval_congr
    intro i
    exact Frame.initial_eval id bits i
  | succ t ih =>
    simpa only [timeFrame, Frame.repeat, Frame.step_eval, stepExpressions,
      Fin.lastCases_last, Expr.eval] using ih

theorem timeFrame_eval (V : NPVerifier) (input : List Bool) (bits : FreeBits V input)
    (hv : WitnessEncoding.Valid bits) (t : Nat) (ht : t ≤ V.horizon input.length) :
    (timeFrame V input t).eval bits = stateEncoding V input (actualRun V input bits t)
      ((WitnessCircuit.validityExpr _).eval bits) := by
  induction t with
  | zero => exact initialFrame_eval V input bits hv
  | succ t ih =>
    have hprev := ih (by omega)
    change ((timeFrame V input t).step (stepExpressions V input)).eval bits = _
    rw [Frame.step_eval_fun, hprev]
    have hs := stepExpressions_eval V input (actualRun V input bits t)
      (actualRun_stepSafe V input bits t (by omega))
      ((WitnessCircuit.validityExpr _).eval bits)
    change (fun i => (stepExpressions V input i).eval
      (stateEncoding V input (actualRun V input bits t)
        ((WitnessCircuit.validityExpr _).eval bits))) = _ at hs
    simpa only [actualRun, BoundedExecution.run_succ] using hs

def mismatchExpr (V : NPVerifier) (input : List Bool) (j : Fin (width V input)) :
    Expr (Fin (width V input + 1)) :=
  if configEncoding (capacity V input.length) (accepting V) ((bitEquiv V input).symm j)
  then .not (.input j.castSucc) else .input j.castSucc

def acceptanceExpr (V : NPVerifier) (input : List Bool) : Expr (Fin (width V input + 1)) :=
  .and (.input (Fin.last (width V input)))
    (.not (Expr.disjoin (List.ofFn (mismatchExpr V input))))

theorem mismatchExpr_eval (V : NPVerifier) (input : List Bool)
    (state : Fin (width V input + 1) → Bool) (j : Fin (width V input)) :
    (mismatchExpr V input j).eval state = true ↔
      state j.castSucc ≠ configEncoding (capacity V input.length) (accepting V)
        ((bitEquiv V input).symm j) := by
  cases ht : configEncoding (capacity V input.length) (accepting V)
      ((bitEquiv V input).symm j) <;> cases hs : state j.castSucc <;>
    simp [mismatchExpr, Expr.eval, ht, hs]

theorem acceptanceExpr_eval (V : NPVerifier) (input : List Bool)
    (state : Fin (width V input + 1) → Bool) :
    (acceptanceExpr V input).eval state = true ↔
      state (Fin.last (width V input)) = true ∧
      ∀ j : Fin (width V input), state j.castSucc =
        configEncoding (capacity V input.length) (accepting V) ((bitEquiv V input).symm j) := by
  have hd : (Expr.disjoin (List.ofFn (mismatchExpr V input))).eval state = true ↔
      ∃ j : Fin (width V input), state j.castSucc ≠
        configEncoding (capacity V input.length) (accepting V) ((bitEquiv V input).symm j) := by
    rw [Expr.eval_disjoin_true]
    constructor
    · rintro ⟨e, he, hv⟩
      obtain ⟨j, rfl⟩ := List.mem_ofFn.mp he
      exact ⟨j, (mismatchExpr_eval V input state j).mp hv⟩
    · rintro ⟨j, hj⟩
      exact ⟨_, List.mem_ofFn.mpr ⟨j, rfl⟩, (mismatchExpr_eval V input state j).mpr hj⟩
  have hz : (Expr.disjoin (List.ofFn (mismatchExpr V input))).eval state = false ↔
      ∀ j : Fin (width V input), state j.castSucc =
        configEncoding (capacity V input.length) (accepting V) ((bitEquiv V input).symm j) := by
    constructor
    · intro h j
      by_contra hj
      have ht := hd.mpr ⟨j, hj⟩
      rw [h] at ht
      contradiction
    · intro h
      cases ht : (Expr.disjoin (List.ofFn (mismatchExpr V input))).eval state with
      | false => rfl
      | true =>
        obtain ⟨j, hj⟩ := hd.mp ht
        exact False.elim (hj (h j))
  simp only [acceptanceExpr, Expr.eval, Bool.and_eq_true, Bool.not_eq_true_eq_eq_false]
  exact and_congr_right (fun _ => hz)

theorem acceptanceExpr_stateEncoding (V : NPVerifier) (input : List Bool)
    (cfg : V.computation.tm.Cfg) (valid : Bool)
    (hcfg : ∀ k, (cfg.stk k).length ≤ capacity V input.length) :
    (acceptanceExpr V input).eval (stateEncoding V input cfg valid) = true ↔
      valid = true ∧ cfg = accepting V := by
  rw [acceptanceExpr_eval]
  constructor
  · rintro ⟨hv, hbits⟩
    refine ⟨by simpa using hv, ?_⟩
    apply MachineCircuit.configEncoding_injective (capacity V input.length)
      cfg (accepting V) hcfg (accepting_stack_le V input)
    funext b
    have h := hbits (bitEquiv V input b)
    simpa [stateEncoding] using h
  · rintro ⟨hv, rfl⟩
    simp [stateEncoding, hv]

def circuitOfVerifier (V : NPVerifier) (input : List Bool) : Circuit :=
  ((timeFrame V input (V.horizon input.length)).step
    (fun _ : Fin 1 => acceptanceExpr V input)).toCircuit 0

@[simp] theorem circuitOfVerifier_inputs (V : NPVerifier) (input : List Bool) :
    (circuitOfVerifier V input).inputs = 2 * V.witnessBound.eval input.length + 1 := rfl

theorem circuitOfVerifier_eval (V : NPVerifier) (input : List Bool) (bits : FreeBits V input) :
    (circuitOfVerifier V input).eval bits =
      (acceptanceExpr V input).eval ((timeFrame V input (V.horizon input.length)).eval bits) := by
  change (((timeFrame V input (V.horizon input.length)).step
    (fun _ : Fin 1 => acceptanceExpr V input)).toCircuit 0).eval bits = _
  rw [Frame.toCircuit_eval, Frame.step_eval]

theorem circuitOfVerifier_accepts_iff (V : NPVerifier) (input : List Bool)
    (bits : FreeBits V input) :
    (circuitOfVerifier V input).eval bits = true ↔
      WitnessEncoding.Valid bits ∧ V.verify (input, WitnessEncoding.decode bits) = true := by
  rw [circuitOfVerifier_eval]
  constructor
  · intro h
    have hvalid := ((acceptanceExpr_eval V input _).mp h).1
    rw [timeFrame_validity] at hvalid
    have hv : WitnessEncoding.Valid bits := (WitnessCircuit.eval_validityExpr bits).mp hvalid
    rw [timeFrame_eval V input bits hv _ le_rfl] at h
    have he := (acceptanceExpr_stateEncoding V input
      (actualRun V input bits (V.horizon input.length)) _
      (actualRun_stack_le V input bits _ le_rfl)).mp h
    exact ⟨hv, (actualRun_accepting_iff V input bits).mp he.2⟩
  · rintro ⟨hv, hverify⟩
    rw [timeFrame_eval V input bits hv _ le_rfl]
    apply (acceptanceExpr_stateEncoding V input
      (actualRun V input bits (V.horizon input.length)) _
      (actualRun_stack_le V input bits _ le_rfl)).mpr
    exact ⟨(WitnessCircuit.eval_validityExpr bits).mpr hv,
      (actualRun_accepting_iff V input bits).mpr hverify⟩

theorem circuitOfVerifier_correct (V : NPVerifier) (input : List Bool) :
    (circuitOfVerifier V input).toFormula.Satisfiable ↔ V.Accepts input := by
  rw [Circuit.toFormula_satisfiable_iff_eval, WitnessEncoding.accepts_iff_valid_assignment]
  change (∃ bits : FreeBits V input, (circuitOfVerifier V input).eval bits = true) ↔ _
  exact exists_congr (fun bits => circuitOfVerifier_accepts_iff V input bits)

theorem mismatchExpr_size_le (V : NPVerifier) (input : List Bool) (j : Fin (width V input)) :
    (mismatchExpr V input j).size ≤ 2 := by
  unfold mismatchExpr
  split <;> simp [Expr.size]

theorem acceptanceExpr_size_le (V : NPVerifier) (input : List Bool) :
    (acceptanceExpr V input).size ≤ 3 * width V input + 4 := by
  have h := Expr.size_disjoin_le (List.ofFn (mismatchExpr V input)) 2 (by
    intro e he
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp he
    exact mismatchExpr_size_le V input j)
  simp only [List.length_ofFn] at h
  simp only [acceptanceExpr, Expr.size]
  omega

theorem stepExpressions_size_le (V : NPVerifier) (input : List Bool)
    (j : Fin (width V input + 1)) :
    (stepExpressions V input j).size ≤ MachineCircuit.expressionCost V.computation.tm.m := by
  refine Fin.lastCases ?_ (fun i => ?_) j
  · simp only [stepExpressions, Fin.lastCases_last, Expr.size, MachineCircuit.expressionCost]
    omega
  · simpa [stepExpressions] using MachineCircuit.stickyExpr_size_le
      (capacity V input.length) V.computation.tm.m ((bitEquiv V input).symm i)

theorem initialExpressions_cost_le (V : NPVerifier) (input : List Bool) :
    Batch.cost (List.ofFn (initialExpressions V input)) ≤
      width V input * (8 * (V.witnessBound.eval input.length + 1) + 15) +
      12 * (V.witnessBound.eval input.length + 1) ^ 2 := by
  rw [Batch.cost_ofFn, Fin.sum_univ_castSucc]
  simp only [initialExpressions, Fin.lastCases_castSucc, Fin.lastCases_last]
  apply Nat.add_le_add
  · calc
      _ ≤ ∑ _ : Fin (width V input), (8 * (V.witnessBound.eval input.length + 1) + 15) := by
        apply Finset.sum_le_sum
        intro i _
        exact WitnessCircuit.size_initExpr_le V input (capacity V input.length)
          ((bitEquiv V input).symm i)
      _ = _ := by simp
  · exact WitnessCircuit.size_validityExpr_le _

theorem circuitOfVerifier_gate_count (V : NPVerifier) (input : List Bool) :
    (circuitOfVerifier V input).gates.length =
      Batch.cost (List.ofFn (initialExpressions V input)) +
      V.horizon input.length * Batch.cost (List.ofFn (stepExpressions V input)) +
      (acceptanceExpr V input).size := by
  change ((timeFrame V input (V.horizon input.length)).step
    (fun _ : Fin 1 => acceptanceExpr V input)).fragment.gates.length = _
  rw [Frame.step_gate_count]
  simp only [timeFrame, Frame.repeat_gate_count, initialFrame, Frame.step_gate_count,
    Frame.initial, Fragment.empty, List.length_nil, Nat.zero_add]
  have hsingle : Batch.cost (List.ofFn (fun _ : Fin 1 => acceptanceExpr V input)) =
      (acceptanceExpr V input).size := by simp [Batch.cost]
  rw [hsingle]

theorem circuitOfVerifier_gates_le (V : NPVerifier) (input : List Bool) :
    (circuitOfVerifier V input).gates.length ≤
      width V input * (8 * (V.witnessBound.eval input.length + 1) + 15) +
      12 * (V.witnessBound.eval input.length + 1) ^ 2 +
      V.horizon input.length * ((width V input + 1) *
        MachineCircuit.expressionCost V.computation.tm.m) + (3 * width V input + 4) := by
  rw [circuitOfVerifier_gate_count]
  exact Nat.add_le_add
    (Nat.add_le_add (initialExpressions_cost_le V input)
      (Nat.mul_le_mul_left _ (Batch.cost_ofFn_le _ _ (stepExpressions_size_le V input))))
    (acceptanceExpr_size_le V input)

def widthPolynomial (V : NPVerifier) : Polynomial Nat :=
  Bounds.configurationWidthPolynomial V.computation.time V.witnessBound
    (Runtime.programPushBound V.computation.tm)
    ((indexing V).labelCount + (indexing V).stateCount) (indexing V).symbolCount

theorem widthPolynomial_eval (V : NPVerifier) (input : List Bool) :
    (widthPolynomial V).eval input.length = width V input := by
  simp [widthPolynomial, width, ConfigIndex.Indexing.width, capacity,
    NPVerifier.horizon, Nat.mul_comm]

def gatePolynomial (V : NPVerifier) : Polynomial Nat :=
  VerifierBounds.machineGatesPolynomial V.computation.time V.witnessBound
    (Runtime.programPushBound V.computation.tm)
    ((indexing V).labelCount + (indexing V).stateCount) (indexing V).symbolCount
    (MachineCircuit.expressionCost V.computation.tm.m)

def formulaPolynomial (V : NPVerifier) : Polynomial Nat :=
  VerifierBounds.machineBitsPolynomial V.computation.time V.witnessBound
    (Runtime.programPushBound V.computation.tm)
    ((indexing V).labelCount + (indexing V).stateCount) (indexing V).symbolCount
    (MachineCircuit.expressionCost V.computation.tm.m)

theorem circuitOfVerifier_gates_le_polynomial (V : NPVerifier) (input : List Bool) :
    (circuitOfVerifier V input).gates.length ≤ (gatePolynomial V).eval input.length := by
  have hw := widthPolynomial_eval V input
  unfold widthPolynomial at hw
  simpa only [gatePolynomial, VerifierBounds.machineGatesPolynomial_eval, hw,
    Bounds.horizonPolynomial_eval, NPVerifier.horizon] using
      circuitOfVerifier_gates_le V input

theorem circuitOfVerifier_formulaBits_length_le (V : NPVerifier) (input : List Bool) :
    (formulaBits (circuitOfVerifier V input).toFormula).length ≤
      (formulaPolynomial V).eval input.length := by
  unfold formulaPolynomial
  apply VerifierBounds.toFormula_bits_le_machinePolynomial
  · exact Nat.le_refl _
  · exact circuitOfVerifier_gates_le_polynomial V input

end UniqueGamesTheorem.Foundations.Complexity.CookLevin.VerifierCircuit

end

end

end OAI
