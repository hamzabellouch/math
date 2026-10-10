import OAI.Computability.BinPacking.CookLevin.ForestStage
import OAI.Computability.BinPacking.CookLevin.TermMachine
import OAI.Computability.BinPacking.CookLevin.VerifierCircuit

namespace OAI

noncomputable section
namespace BinPackingGames.Foundations.Complexity.CookLevin.ProducerInvariant

open StatementCircuit CircuitBatch PostfixModel PostfixAlignment

structure Snapshot where
  current : Nat
  roots : List Nat
  reversedRecords : List Bool
  deriving DecidableEq

private theorem snapshot_ext {s t : Snapshot} (hc : s.current = t.current)
    (hr : s.roots = t.roots) (hg : s.reversedRecords = t.reversedRecords) : s = t := by
  cases s
  cases t
  simp_all

variable {inputs oldWidth newWidth width : Nat}

def snapshot (f : Frame inputs width) : Snapshot where
  current := inputs + f.fragment.gates.length
  roots := List.ofFn (fun i => (f.wires i).val)
  reversedRecords := (recordsBits (gateRecords inputs f.fragment.gates)).reverse

def next (f : Frame inputs width) : Nat := inputs + f.fragment.gates.length
def rootValues (f : Frame inputs width) : List Nat := List.ofFn (fun i => (f.wires i).val)
def recordBits (f : Frame inputs width) : List Bool :=
  recordsBits (gateRecords inputs f.fragment.gates)

def Snapshot.currentBits (s : Snapshot) : List Bool := encodeWord s.current
def Snapshot.rootBits (s : Snapshot) : List Bool := encodeWords s.roots

def lowerStage (s : Snapshot) (tokens : List Token) : Option Snapshot := do
  let (next, reversedRoots, gates) ← compileTokens s.current [] tokens
  pure ⟨next, reversedRoots.reverse,
    (recordsBits (gateRecords s.current gates)).reverse ++ s.reversedRecords⟩

def stage (es : Fin newWidth → Expr (Fin oldWidth)) (s : Snapshot) : Option Snapshot :=
  lowerStage s (forestTokens (fun i => s.roots[i.val]?.getD 0) (List.ofFn es))

theorem gateRecords_append (start : Nat) (first rest : List Gate) :
    gateRecords start (first ++ rest) =
      gateRecords start first ++ gateRecords (start + first.length) rest := by
  induction first generalizing start with
  | nil => simp [gateRecords]
  | cons g gs ih =>
    simp [gateRecords, ih, Nat.add_comm, Nat.add_left_comm]

theorem recordsBits_append (first rest : List CircuitProducerModel.Record) :
    recordsBits (first ++ rest) = recordsBits first ++ recordsBits rest := by
  simp only [recordsBits, recordsWords, List.flatMap_append, encodeWords_append]

theorem step_roots (f : Frame inputs oldWidth) (es : Fin newWidth → Expr (Fin oldWidth)) :
    (snapshot (f.step es)).roots =
      Batch.roots (snapshot f).current (List.ofFn es) := by
  apply List.ext_getElem
  · simp [snapshot]
  · intro i hi hj
    simp only [snapshot, List.getElem_ofFn, Frame.step, Batch.rootAt]

theorem lowerStage_snapshot (f : Frame inputs oldWidth)
    (es : Fin newWidth → Expr (Fin oldWidth)) :
    lowerStage (snapshot f)
      (forestTokens (fun i => (f.wires i).val) (List.ofFn es)) =
      some (snapshot (f.step es)) := by
  rw [lowerStage, compile_forestTokens]
  simp only [List.append_nil]
  change some (Snapshot.mk ((snapshot f).current + Batch.cost (List.ofFn es))
    (Batch.roots (snapshot f).current (List.ofFn es)).reverse.reverse
    ((recordsBits (gateRecords (snapshot f).current
      (Batch.gates (fun i => (f.wires i).val) (snapshot f).current (List.ofFn es)))).reverse ++
      (snapshot f).reversedRecords)) = some (snapshot (f.step es))
  rw [List.reverse_reverse]
  apply congrArg some
  apply snapshot_ext
  · simp [snapshot, Frame.step_gate_count, Nat.add_assoc]
  · exact (step_roots f es).symm
  · simp only [snapshot, Frame.step, Fragment.append, gateRecords_append,
      recordsBits_append, List.reverse_append]

theorem stage_snapshot (f : Frame inputs oldWidth)
    (es : Fin newWidth → Expr (Fin oldWidth)) :
    stage es (snapshot f) = some (snapshot (f.step es)) := by
  have hw : (fun i : Fin oldWidth => (snapshot f).roots[i.val]?.getD 0) =
      (fun i => (f.wires i).val) := by
    funext i
    simp [snapshot, i.isLt]
  unfold stage
  rw [hw]
  exact lowerStage_snapshot f es

def stages (es : Fin width → Expr (Fin width)) : Nat → Snapshot → Option Snapshot
  | 0, s => some s
  | t + 1, s => do
    let previous ← stages es t s
    stage es previous

theorem stages_snapshot (f : Frame inputs width)
    (es : Fin width → Expr (Fin width)) (t : Nat) :
    stages es t (snapshot f) = some (snapshot (f.repeat es t)) := by
  induction t with
  | zero => rfl
  | succ t ih =>
    simp only [stages, ih, Frame.repeat]
    exact stage_snapshot _ _

theorem compile_frameForest (f : Frame inputs oldWidth)
    (es : Fin newWidth → Expr (Fin oldWidth)) :
    compileTokens (next f) []
      (forestTokens (fun i => (f.wires i).val) (List.ofFn es)) =
      some (next (f.step es), (rootValues (f.step es)).reverse,
        Batch.gates (fun i => (f.wires i).val) (next f) (List.ofFn es)) := by
  have hr : rootValues (f.step es) = Batch.roots (next f) (List.ofFn es) :=
    step_roots f es
  rw [compile_forestTokens, hr]
  simp only [List.append_nil, next, Frame.step_gate_count, Nat.add_assoc]

theorem recordBits_step (f : Frame inputs oldWidth)
    (es : Fin newWidth → Expr (Fin oldWidth)) :
    recordBits (f.step es) = recordBits f ++
      recordsBits (gateRecords (next f)
        (Batch.gates (fun i => (f.wires i).val) (next f) (List.ofFn es))) := by
  simp only [recordBits, Frame.step, Fragment.append, gateRecords_append,
    recordsBits_append, next]

theorem step_repeat (f : Frame inputs width)
    (es : Fin width → Expr (Fin width)) (n : Nat) :
    (f.step es).repeat es n = f.repeat es (n + 1) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [Frame.repeat, ih]

def circuitOutput (inputs : Nat) (s : Snapshot) : List Bool :=
  encodeWords [s.current, s.current - inputs, s.roots.headD 0] ++
    s.reversedRecords.reverse

theorem circuitOutput_snapshot (f : Frame inputs 1) :
    circuitOutput inputs (snapshot f) = circuitBits (f.toCircuit 0) := by
  simp [circuitOutput, snapshot, circuitBits, circuitWords, Circuit.records,
    Frame.toCircuit, Fragment.toCircuit, Circuit.wires, List.ofFn_succ,
    recordsBits, encodeWords, List.append_assoc]

def finalFrame (V : NPVerifier) (input : List Bool) :
    Frame (2 * V.witnessBound.eval input.length + 1) 1 :=
  (VerifierCircuit.timeFrame V input (V.horizon input.length)).step
    (fun _ : Fin 1 => VerifierCircuit.acceptanceExpr V input)

theorem finalFrame_circuit (V : NPVerifier) (input : List Bool) :
    (finalFrame V input).toCircuit 0 = VerifierCircuit.circuitOfVerifier V input := rfl

theorem verifier_stages (V : NPVerifier) (input : List Bool) :
    (do
      let initialized ← stage (VerifierCircuit.initialExpressions V input)
        (snapshot (Frame.initial (id : Fin (2 * V.witnessBound.eval input.length + 1) →
          Fin (2 * V.witnessBound.eval input.length + 1))))
      let timed ← stages (VerifierCircuit.stepExpressions V input)
        (V.horizon input.length) initialized
      stage (fun _ : Fin 1 => VerifierCircuit.acceptanceExpr V input) timed) =
      some (snapshot (finalFrame V input)) := by
  rw [stage_snapshot]
  change (do
    let timed ← stages (VerifierCircuit.stepExpressions V input)
      (V.horizon input.length) (snapshot (VerifierCircuit.initialFrame V input))
    stage (fun _ : Fin 1 => VerifierCircuit.acceptanceExpr V input) timed) = _
  rw [stages_snapshot]
  change stage (fun _ : Fin 1 => VerifierCircuit.acceptanceExpr V input)
    (snapshot (VerifierCircuit.timeFrame V input (V.horizon input.length))) = _
  exact stage_snapshot _ _

theorem verifier_output (V : NPVerifier) (input : List Bool) :
    circuitOutput (2 * V.witnessBound.eval input.length + 1)
      (snapshot (finalFrame V input)) =
      circuitBits (VerifierCircuit.circuitOfVerifier V input) :=
  circuitOutput_snapshot (finalFrame V input)

theorem snapshot_root_mem_lt (f : Frame inputs width) (r : Nat)
    (hr : r ∈ (snapshot f).roots) : r < (snapshot f).current := by
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hr
  exact (f.wires i).isLt

theorem snapshot_rootBits_length_le (f : Frame inputs width) :
    (snapshot f).rootBits.length ≤ width * ((snapshot f).current + 1) := by
  have h := encodeWords_length_le (snapshot f).roots (snapshot f).current
    (fun r hr => Nat.le_of_lt (snapshot_root_mem_lt f r hr))
  simpa only [Snapshot.rootBits, snapshot, List.length_ofFn] using h

theorem snapshot_records_length_le (f : Frame inputs width) :
    (snapshot f).reversedRecords.length ≤
      4 * f.fragment.gates.length * ((snapshot f).current + 5) := by
  have h := encodeWords_length_le
    (recordsWords (gateRecords inputs f.fragment.gates))
    (inputs + f.fragment.gates.length + 4)
    (gateRecords_fields_le inputs f.fragment.gates f.fragment.ordered)
  simpa only [snapshot, List.length_reverse, recordsBits, recordsWords_length,
    gateRecords_length, Nat.add_assoc] using h

theorem snapshot_lengths_le (f : Frame inputs width) (B : Nat)
    (hc : (snapshot f).current ≤ B) (hg : f.fragment.gates.length ≤ B)
    (hw : width ≤ B) :
    (snapshot f).currentBits.length ≤ 4 * (B + 6)^2 ∧
    (snapshot f).rootBits.length ≤ 4 * (B + 6)^2 ∧
    (snapshot f).reversedRecords.length ≤ 4 * (B + 6)^2 := by
  refine ⟨?_, ?_, ?_⟩
  · simp only [Snapshot.currentBits, encodeWord_length]
    nlinarith
  · apply (snapshot_rootBits_length_le f).trans
    have hm := Nat.mul_le_mul hw (Nat.add_le_add_right hc 1)
    nlinarith
  · apply (snapshot_records_length_le f).trans
    have hm := Nat.mul_le_mul (Nat.mul_le_mul_left 4 hg) (Nat.add_le_add_right hc 5)
    nlinarith

theorem stage_tokenBits_length_le (f : Frame inputs oldWidth)
    (es : Fin newWidth → Expr (Fin oldWidth)) (B : Nat)
    (hc : (snapshot f).current ≤ B) (he : Batch.cost (List.ofFn es) ≤ B) :
    (tokenBits (forestTokens (fun i => (f.wires i).val) (List.ofFn es))).length ≤
      4 * (B + 6)^2 := by
  apply (forest_tokenBits_length_le _ _ (snapshot f).current
    (fun i => (f.wires i).isLt)).trans
  have hmax : max 5 (snapshot f).current + 1 ≤ B + 6 := by omega
  have hm := Nat.mul_le_mul (Nat.mul_le_mul_left 2 he) hmax
  nlinarith

theorem stage_countBits_length_le (f : Frame inputs oldWidth)
    (es : Fin newWidth → Expr (Fin oldWidth)) (B : Nat)
    (he : Batch.cost (List.ofFn es) ≤ B) :
    (encodeWord ((forestTokens (fun i => (f.wires i).val) (List.ofFn es)).length)).length ≤
      4 * (B + 6)^2 := by
  simp only [encodeWord_length, forestTokens_length]
  nlinarith

def budgetPolynomial (V : NPVerifier) : Polynomial Nat :=
  WitnessEncoding.freeInputPolynomial V.witnessBound + VerifierCircuit.gatePolynomial V +
    VerifierCircuit.widthPolynomial V + 1

def tapePolynomial (V : NPVerifier) : Polynomial Nat :=
  4 * (budgetPolynomial V + 6)^2

theorem budgetPolynomial_eval (V : NPVerifier) (input : List Bool) :
    (budgetPolynomial V).eval input.length =
      (2 * V.witnessBound.eval input.length + 1) +
      (VerifierCircuit.gatePolynomial V).eval input.length +
      VerifierCircuit.width V input + 1 := by
  simp only [budgetPolynomial, Polynomial.eval_add, Polynomial.eval_one,
    WitnessEncoding.freeInputPolynomial_eval, VerifierCircuit.widthPolynomial_eval]

theorem tapePolynomial_eval (V : NPVerifier) (n : Nat) :
    (tapePolynomial V).eval n = 4 * ((budgetPolynomial V).eval n + 6)^2 := by
  simp [tapePolynomial]

theorem freeFrame_lengths_le (V : NPVerifier) (input : List Bool) :
    let s := snapshot (Frame.initial (id : Fin (2 * V.witnessBound.eval input.length + 1) →
      Fin (2 * V.witnessBound.eval input.length + 1)))
    s.currentBits.length ≤ (tapePolynomial V).eval input.length ∧
    s.rootBits.length ≤ (tapePolynomial V).eval input.length ∧
    s.reversedRecords.length ≤ (tapePolynomial V).eval input.length := by
  dsimp only
  rw [tapePolynomial_eval]
  have hb := budgetPolynomial_eval V input
  apply snapshot_lengths_le
  · change _ + 0 ≤ _
    omega
  · change 0 ≤ _
    omega
  · omega

theorem timeFrame_gate_count (V : NPVerifier) (input : List Bool) (t : Nat) :
    (VerifierCircuit.timeFrame V input t).fragment.gates.length =
      Batch.cost (List.ofFn (VerifierCircuit.initialExpressions V input)) +
      t * Batch.cost (List.ofFn (VerifierCircuit.stepExpressions V input)) := by
  simp only [VerifierCircuit.timeFrame, Frame.repeat_gate_count,
    VerifierCircuit.initialFrame, Frame.step_gate_count, Frame.initial,
    Fragment.empty, List.length_nil, Nat.zero_add]

theorem timeFrame_gates_le (V : NPVerifier) (input : List Bool) (t : Nat)
    (ht : t ≤ V.horizon input.length) :
    (VerifierCircuit.timeFrame V input t).fragment.gates.length ≤
      (VerifierCircuit.gatePolynomial V).eval input.length := by
  apply le_trans ?_ (VerifierCircuit.circuitOfVerifier_gates_le_polynomial V input)
  rw [timeFrame_gate_count, VerifierCircuit.circuitOfVerifier_gate_count]
  have hm := Nat.mul_le_mul_right
    (Batch.cost (List.ofFn (VerifierCircuit.stepExpressions V input))) ht
  omega

theorem timeFrame_current_le (V : NPVerifier) (input : List Bool) (t : Nat)
    (ht : t ≤ V.horizon input.length) :
    next (VerifierCircuit.timeFrame V input t) ≤ (budgetPolynomial V).eval input.length := by
  have hg := timeFrame_gates_le V input t ht
  have hb := budgetPolynomial_eval V input
  unfold next
  omega

theorem transition_cost_le_budget (V : NPVerifier) (input : List Bool)
    (hT : 0 < V.horizon input.length) :
    Batch.cost (List.ofFn (VerifierCircuit.stepExpressions V input)) ≤
      (budgetPolynomial V).eval input.length := by
  have hg := VerifierCircuit.circuitOfVerifier_gates_le_polynomial V input
  rw [VerifierCircuit.circuitOfVerifier_gate_count] at hg
  have hb := budgetPolynomial_eval V input
  have hm := Nat.mul_le_mul_right
    (Batch.cost (List.ofFn (VerifierCircuit.stepExpressions V input)))
    (show 1 ≤ V.horizon input.length by omega)
  omega

theorem timeFrame_lengths_le (V : NPVerifier) (input : List Bool) (t : Nat)
    (ht : t ≤ V.horizon input.length) :
    let s := snapshot (VerifierCircuit.timeFrame V input t)
    s.currentBits.length ≤ (tapePolynomial V).eval input.length ∧
    s.rootBits.length ≤ (tapePolynomial V).eval input.length ∧
    s.reversedRecords.length ≤ (tapePolynomial V).eval input.length := by
  dsimp only
  rw [tapePolynomial_eval]
  have hg := timeFrame_gates_le V input t ht
  have hb := budgetPolynomial_eval V input
  apply snapshot_lengths_le
  · change _ + _ ≤ _
    omega
  · omega
  · omega

theorem initial_tokens_length_le (V : NPVerifier) (input : List Bool) :
    (tokenBits (forestTokens (fun i : Fin (2 * V.witnessBound.eval input.length + 1) => i.val)
      (List.ofFn (VerifierCircuit.initialExpressions V input)))).length ≤
      (tapePolynomial V).eval input.length := by
  rw [tapePolynomial_eval]
  have hg := VerifierCircuit.circuitOfVerifier_gates_le_polynomial V input
  rw [VerifierCircuit.circuitOfVerifier_gate_count] at hg
  have hb := budgetPolynomial_eval V input
  apply stage_tokenBits_length_le (Frame.initial id)
  · change _ + 0 ≤ _
    omega
  · omega

theorem transition_tokens_length_le (V : NPVerifier) (input : List Bool) (t : Nat)
    (ht : t < V.horizon input.length) :
    (tokenBits (forestTokens
      (fun i => ((VerifierCircuit.timeFrame V input t).wires i).val)
      (List.ofFn (VerifierCircuit.stepExpressions V input)))).length ≤
      (tapePolynomial V).eval input.length := by
  rw [tapePolynomial_eval]
  have hg := VerifierCircuit.circuitOfVerifier_gates_le_polynomial V input
  rw [VerifierCircuit.circuitOfVerifier_gate_count] at hg
  have hp := timeFrame_gates_le V input t (Nat.le_of_lt ht)
  have hb := budgetPolynomial_eval V input
  have hm := Nat.mul_le_mul_right
    (Batch.cost (List.ofFn (VerifierCircuit.stepExpressions V input)))
    (show 1 ≤ V.horizon input.length by omega)
  apply stage_tokenBits_length_le (VerifierCircuit.timeFrame V input t)
  · change _ + _ ≤ _
    omega
  · omega

theorem acceptance_tokens_length_le (V : NPVerifier) (input : List Bool) :
    (tokenBits (forestTokens
      (fun i => ((VerifierCircuit.timeFrame V input (V.horizon input.length)).wires i).val)
      (List.ofFn (fun _ : Fin 1 => VerifierCircuit.acceptanceExpr V input)))).length ≤
      (tapePolynomial V).eval input.length := by
  rw [tapePolynomial_eval]
  have hg := VerifierCircuit.circuitOfVerifier_gates_le_polynomial V input
  rw [VerifierCircuit.circuitOfVerifier_gate_count] at hg
  have hp := timeFrame_gates_le V input (V.horizon input.length) le_rfl
  have hb := budgetPolynomial_eval V input
  apply stage_tokenBits_length_le
  · change _ + _ ≤ _
    omega
  · simp only [List.ofFn_succ, List.ofFn_zero, Batch.cost_cons, Batch.cost_nil,
      Nat.add_zero]
    omega

theorem finalFrame_lengths_le (V : NPVerifier) (input : List Bool) :
    let s := snapshot (finalFrame V input)
    s.currentBits.length ≤ (tapePolynomial V).eval input.length ∧
    s.rootBits.length ≤ (tapePolynomial V).eval input.length ∧
    s.reversedRecords.length ≤ (tapePolynomial V).eval input.length := by
  dsimp only
  rw [tapePolynomial_eval]
  have hg := VerifierCircuit.circuitOfVerifier_gates_le_polynomial V input
  change (finalFrame V input).fragment.gates.length ≤ _ at hg
  have hb := budgetPolynomial_eval V input
  apply snapshot_lengths_le
  · change _ + _ ≤ _
    omega
  · omega
  · omega

def stageEnvelopePolynomial (V : NPVerifier) : Polynomial Nat :=
  Bounds.capacityPolynomial V.computation.time V.witnessBound
    (Runtime.programPushBound V.computation.tm) + budgetPolynomial V + tapePolynomial V + 1

theorem stageEnvelopePolynomial_eval (V : NPVerifier) (input : List Bool) :
    (stageEnvelopePolynomial V).eval input.length =
      VerifierCircuit.capacity V input.length + (budgetPolynomial V).eval input.length +
      (tapePolynomial V).eval input.length + 1 := by
  simp [stageEnvelopePolynomial, VerifierCircuit.capacity, NPVerifier.horizon, Nat.mul_comm]

theorem timeFrame_stageEnvelope (V : NPVerifier) (input : List Bool) (t : Nat)
    (ht : t < V.horizon input.length) :
    let B := (stageEnvelopePolynomial V).eval input.length
    let f := VerifierCircuit.timeFrame V input t
    VerifierCircuit.capacity V input.length ≤ B ∧ next f ≤ B ∧
    Batch.cost (List.ofFn (VerifierCircuit.stepExpressions V input)) ≤ B ∧
    (snapshot f).rootBits.length ≤ B ∧
    (tokenBits (forestTokens (fun i => (f.wires i).val)
      (List.ofFn (VerifierCircuit.stepExpressions V input)))).length ≤ B := by
  dsimp only
  have hc := timeFrame_current_le V input t (Nat.le_of_lt ht)
  have hcost := transition_cost_le_budget V input (by omega)
  have hr := (timeFrame_lengths_le V input t (Nat.le_of_lt ht)).2.1
  have htoks := transition_tokens_length_le V input t ht
  rw [stageEnvelopePolynomial_eval]
  exact ⟨by omega, by omega, by omega, by omega, by omega⟩

theorem verifier_circuitBits_length_le (V : NPVerifier) (input : List Bool) :
    (circuitBits (VerifierCircuit.circuitOfVerifier V input)).length ≤
      (tapePolynomial V).eval input.length := by
  rw [tapePolynomial_eval]
  apply (circuitBits_length_le (VerifierCircuit.circuitOfVerifier V input)).trans
  have hg := VerifierCircuit.circuitOfVerifier_gates_le_polynomial V input
  have hb := budgetPolynomial_eval V input
  have hc : (VerifierCircuit.circuitOfVerifier V input).wires ≤
      (budgetPolynomial V).eval input.length := by
    simp only [Circuit.wires, VerifierCircuit.circuitOfVerifier_inputs]
    omega
  have hgb : (VerifierCircuit.circuitOfVerifier V input).gates.length ≤
      (budgetPolynomial V).eval input.length := by omega
  have hm := Nat.mul_le_mul (Nat.add_le_add_left (Nat.mul_le_mul_left 4 hgb) 3)
    (Nat.add_le_add_right hc 5)
  nlinarith

section GenericTransition

variable {K Λ σ : Type} {Γ : K → Type}
  [DecidableEq K] [DecidableEq Λ] [DecidableEq σ]
  [Fintype Λ] [Fintype σ] [∀ k, Fintype (Γ k)] [∀ k, DecidableEq (Γ k)]

def stepExpressions (indexing : ConfigIndex.Indexing Γ Λ σ)
    (program : Λ → Turing.TM2.Stmt Γ Λ σ) (S : Nat) :
    Fin (indexing.width S + 1) → Expr (Fin (indexing.width S + 1)) :=
  Fin.lastCases (.input (Fin.last (indexing.width S)))
    (fun j => (MachineCircuit.stickyExpr S program
      ((indexing.configIndexEquiv S).symm j)).rename
        (fun b => (indexing.configIndexEquiv S b).castSucc))

def transitionTokens (indexing : ConfigIndex.Indexing Γ Λ σ)
    (program : Λ → Turing.TM2.Stmt Γ Λ σ) (S : Nat) (roots : List Nat) : List Token :=
  TransitionTemplate.forestTokens indexing roots S program ++
    [.input (TransitionTemplate.rootLookup roots (indexing.width S))]

theorem transitionTokens_eq (indexing : ConfigIndex.Indexing Γ Λ σ)
    (program : Λ → Turing.TM2.Stmt Γ Λ σ) (S : Nat) (roots : List Nat) :
    transitionTokens indexing program S roots =
      forestTokens (fun i => roots[i.val]?.getD 0)
        (List.ofFn (stepExpressions indexing program S)) := by
  rw [List.ofFn_succ']
  simp only [stepExpressions, Fin.lastCases_castSucc, Fin.lastCases_last,
    List.concat_eq_append, forestTokens, List.flatMap_append, List.flatMap_cons,
    List.flatMap_nil, exprTokens, List.append_nil]
  unfold transitionTokens
  rw [TransitionTemplate.forestTokens_eq]
  congr 1
  simp only [TransitionTemplate.outputOrder, List.map_map, List.ofFn_eq_map,
    forestTokens, List.flatMap_map]
  apply List.flatMap_congr
  intro i _
  rw [exprTokens_rename]
  rfl

theorem compile_transitionTokens (indexing : ConfigIndex.Indexing Γ Λ σ)
    (program : Λ → Turing.TM2.Stmt Γ Λ σ) (S : Nat)
    (f : Frame inputs (indexing.width S + 1)) :
    compileTokens (next f) [] (transitionTokens indexing program S (rootValues f)) =
      some (next (f.step (stepExpressions indexing program S)),
        (rootValues (f.step (stepExpressions indexing program S))).reverse,
        Batch.gates (fun i => (f.wires i).val) (next f)
          (List.ofFn (stepExpressions indexing program S))) := by
  rw [transitionTokens_eq]
  have hw : (fun i : Fin (indexing.width S + 1) => (rootValues f)[i.val]?.getD 0) =
      (fun i => (f.wires i).val) := by
    funext i
    unfold rootValues
    rw [List.getElem?_eq_getElem (by simpa only [List.length_ofFn] using i.isLt),
      List.getElem_ofFn]
    rfl
  rw [hw]
  exact compile_frameForest f _

end GenericTransition

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

theorem stepExpressions_verifier (V : NPVerifier) (input : List Bool) :
    stepExpressions (VerifierCircuit.indexing V) V.computation.tm.m
      (VerifierCircuit.capacity V input.length) =
      VerifierCircuit.stepExpressions V input := rfl

end BinPackingGames.Foundations.Complexity.CookLevin.ProducerInvariant

end

namespace BinPackingGames.Foundations.Complexity.CookLevin.TransitionArena

open Turing MachineComposition

inductive Extra
  | cursor | capacity | position | address | value | scratch | copy | saveLeft | saveRight
  | countdown | q | raw
  deriving DecidableEq

protected abbrev Extra.enumList : List Extra := [.cursor, .capacity, .position, .address, .value,
  .scratch, .copy, .saveLeft, .saveRight, .countdown, .q, .raw]

protected theorem Extra.enumList_getElem?_ctorIdx_eq (x : Extra) :
    Extra.enumList[x.ctorIdx]? = some x := by
  cases x <;> rfl

protected theorem Extra.enumList_nodup : Extra.enumList.Nodup := by decide

instance : Fintype Extra where
  elems := ⟨Extra.enumList, Extra.enumList_nodup⟩
  complete x := by cases x <;> decide

abbrev Tape := ForestStage.Tape ⊕ Extra
abbrev Alphabet (_ : Tape) := Bool
abbrev State := TermMachine.State

def forestPorts : ForestStage.Tape ↪ Tape :=
  ⟨Sum.inl, Sum.inl_injective⟩

def termTape : TermMachine.Tape → Tape
  | .cursor => .inr .cursor
  | .capacity => .inr .capacity
  | .roots => .inl .rootTable
  | .count => .inl (.lower .remaining)
  | .reversed => .inl .tokens
  | .position => .inr .position
  | .address => .inr .address
  | .value => .inr .value
  | .scratch => .inr .scratch
  | .copy => .inr .copy
  | .saveLeft => .inr .saveLeft
  | .saveRight => .inr .saveRight

def termPorts : TermMachine.Tape ↪ Tape where
  toFun := termTape
  inj' := by intro a b h; cases a <;> cases b <;> simp_all [termTape]

@[simp] theorem termPorts_apply (tape : TermMachine.Tape) : termPorts tape = termTape tape := rfl

def termInput (S : Nat) (snapshot : ProducerInvariant.Snapshot) : TermMachine.Input :=
  ⟨0, S, snapshot.roots⟩

def tapes (base : Tape → List Bool) (S remaining : Nat)
    (snapshot : ProducerInvariant.Snapshot) : Tape → List Bool
  | .inl (.lower .current) => encodeWord snapshot.current
  | .inl (.lower .remaining) => encodeWord 0
  | .inl (.lower _) => []
  | .inl .tokens => []
  | .inl .records => snapshot.reversedRecords
  | .inl .rootTable => encodeWords snapshot.roots
  | .inr .cursor => encodeWord 0
  | .inr .capacity => encodeWord S
  | .inr .countdown => encodeWord remaining
  | .inr .q => base (.inr .q)
  | .inr .raw => base (.inr .raw)
  | .inr _ => []

def finishTapes (base : Tape → List Bool) (S : Nat)
    (snapshot : ProducerInvariant.Snapshot) : Tape → List Bool :=
  Function.update (tapes base S 0 snapshot) (.inr .countdown) []

@[simp] theorem tapes_q (base : Tape → List Bool) (S remaining : Nat)
    (snapshot : ProducerInvariant.Snapshot) : tapes base S remaining snapshot (.inr .q) =
      base (.inr .q) := rfl

@[simp] theorem tapes_raw (base : Tape → List Bool) (S remaining : Nat)
    (snapshot : ProducerInvariant.Snapshot) : tapes base S remaining snapshot (.inr .raw) =
      base (.inr .raw) := rfl

@[simp] theorem tapes_capacity (base : Tape → List Bool) (S remaining : Nat)
    (snapshot : ProducerInvariant.Snapshot) :
    tapes base S remaining snapshot (.inr .capacity) = encodeWord S := rfl

theorem termFrame (base : Tape → List Bool) (S remaining : Nat)
    (snapshot : ProducerInvariant.Snapshot) :
    TermMachine.Frame (termInput S snapshot)
      (fun tape => tapes base S remaining snapshot (termPorts tape)) := by
  refine ⟨rfl, rfl, rfl, ?_⟩
  intro tape ht
  cases tape <;> simp_all [TermMachine.work, termTape, tapes]

theorem tapes_countdown_tail (base : Tape → List Bool) (S remaining : Nat)
    (snapshot : ProducerInvariant.Snapshot) :
    Function.update (tapes base S (remaining + 1) snapshot) (.inr .countdown)
      (tapes base S (remaining + 1) snapshot (.inr .countdown)).tail =
        tapes base S remaining snapshot := by
  funext tape
  cases tape with
  | inl tape =>
    cases tape with
    | lower tape => cases tape <;> simp [tapes]
    | tokens => simp [tapes]
    | records => simp [tapes]
    | rootTable => simp [tapes]
  | inr tape => cases tape <;> simp [tapes, encodeWord, List.replicate_succ]

def preparedTapes (base : Tape → List Bool) (S remaining : Nat)
    (snapshot : ProducerInvariant.Snapshot) (tokens : List PostfixModel.Token) : Tape → List Bool :=
  Function.update
    (Function.update (tapes base S remaining snapshot) (.inl .tokens)
      (PostfixModel.tokenBits tokens).reverse)
    (.inl (.lower .remaining)) (encodeWord tokens.length)

theorem place_emitTapes (base : Tape → List Bool) (S remaining : Nat)
    (snapshot : ProducerInvariant.Snapshot) (tokens : List PostfixModel.Token) :
    ForestPlacement.fill termPorts (tapes base S remaining snapshot)
      (TermMachine.emitTapes (fun tape => tapes base S remaining snapshot (termPorts tape)) tokens) =
      preparedTapes base S remaining snapshot tokens := by
  simp only [TermMachine.emitTapes, ForestPlacement.fill_update, ForestPlacement.fill_self]
  simp [termTape, tapes, preparedTapes, encodeWord]

theorem fill_forest (base : Tape → List Bool) (contents : ForestStage.Tape → List Bool) :
    ForestPlacement.fill forestPorts base contents =
      fun tape => match tape with
      | .inl t => contents t
      | .inr t => base (.inr t) := by
  funext tape
  cases tape with
  | inl t => exact ForestPlacement.fill_at forestPorts base contents t
  | inr t =>
    exact ForestPlacement.fill_other forestPorts base contents (.inr t)
      (by intro i; simp [forestPorts])

end BinPackingGames.Foundations.Complexity.CookLevin.TransitionArena

end OAI
