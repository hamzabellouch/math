import Mathlib
import OAI.Computability.DirectedFeedback.Machines.PoweringMachineRowBody

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section

section

namespace DFVSGames.Foundations.Complexity.PoweringMachineOuterLoop

open Turing MachineComposition PCP

variable {K Λ : Type} [DecidableEq K] {vertices d : Nat}

abbrev Placement (K : Type) (n : Nat) := PoweringMachineTapes.Tape (PoweringMachineRowBody.capacity n) → K
abbrev State := PoweringMachineVertex.State

structure Ready (graph : PortTables.Table vertices d) (n : Nat) (placement : Placement K n)
    (base : K → List Bool) : Prop where
  table : base (placement (.inl 0)) = PortTables.tableBits graph
  scratch : base (placement (.inl 5)) = []
  leftCopy : base (placement (.inl 8)) = []
  rightCopy : base (placement (.inl 9)) = []
  data : base (placement (.inl 10)) = []

def counter {n : Nat} (placement : Placement K n) (base : K → List Bool) (remaining : Nat) : K → List Bool :=
  MachineUnaryCounter.counterTapes (placement (.inl 1)) base remaining []

theorem counter_other {n : Nat} (placement : Placement K n) (distinct : Function.Injective placement)
    (base : K → List Bool) (remaining : Nat) (j : Fin 11) (hj : j ≠ 1) :
    counter placement base remaining (placement (.inl j)) = base (placement (.inl j)) := by
  apply MachineUnaryCounter.counterTapes_other
  intro h
  exact hj (Sum.inl.inj (distinct h))

theorem ready_vertex (graph : PortTables.Table vertices d) (n : Nat)
    (placement : Placement K n) (distinct : Function.Injective placement)
    (base : K → List Bool) (ready : Ready graph n placement base) (vertex : Fin vertices) :
    PoweringMachineRowBody.Ready graph n placement vertex [] (counter placement base vertex.val) := by
  constructor
  · constructor
    · rw [counter_other placement distinct base vertex.val 0 (by decide)]
      exact ready.table
    · simp only [counter, MachineUnaryCounter.counterTapes_counter]
    · rw [counter_other placement distinct base vertex.val 5 (by decide)]
      exact ready.scratch
    · rw [counter_other placement distinct base vertex.val 8 (by decide)]
      exact ready.leftCopy
    · rw [counter_other placement distinct base vertex.val 9 (by decide)]
      exact ready.rightCopy
  · rw [counter_other placement distinct base vertex.val 10 (by decide)]
    exact ready.data

omit [DecidableEq K] in
theorem ready_of_vertex (graph : PortTables.Table vertices d) (n : Nat)
    (placement : Placement K n) (base : K → List Bool) (vertex : Fin vertices)
    (ready : PoweringMachineRowBody.Ready graph n placement vertex [] base) :
    Ready graph n placement base :=
  ⟨ready.1.table, ready.1.scratch, ready.1.leftCopy, ready.1.rightCopy, ready.2⟩

def vertexStart (d n : Nat) (labels : PoweringMachineVertex.Label d n → Λ) (guardLabel : Λ) : Λ :=
  (PoweringMachineVertex.entry d n labels (some guardLabel)).getD guardLabel

theorem vertexEntry (d n : Nat) (labels : PoweringMachineVertex.Label d n → Λ) (guardLabel : Λ) :
    PoweringMachineVertex.entry d n labels (some guardLabel) =
      some (vertexStart d n labels guardLabel) := by
  unfold vertexStart PoweringMachineVertex.entry PoweringMachineVertex.sequenceEntry
  have h : ∀ (commands : List (PoweringMachineVertex.Command d n))
      (labels : MachineFiniteSequence.Label PoweringMachineVertex.LocalLabel commands → Λ),
      MachineFiniteSequence.entry PoweringMachineVertex.LocalLabel
        (fun j => PoweringMachineRowBody.entry n
          (PoweringMachineVertex.ports j) (PoweringMachineVertex.direction j))
        commands labels (some guardLabel) =
      some ((MachineFiniteSequence.entry PoweringMachineVertex.LocalLabel
        (fun j => PoweringMachineRowBody.entry n
          (PoweringMachineVertex.ports j) (PoweringMachineVertex.direction j))
        commands labels (some guardLabel)).getD guardLabel) := by
    intro commands labels
    cases commands <;> rfl
  exact h _ labels

def bridge (d n : Nat) (labels : PoweringMachineVertex.Label d n → Λ) (guardLabel : Λ) :
    TM2.Stmt (fun _ : K => Bool) Λ (State d n) :=
  .goto (fun _ => vertexStart d n labels guardLabel)

def finalTapes (graph : PortTables.Table vertices d) (n : Nat) (placement : Placement K n)
    (output : K) : (remaining : Nat) → remaining ≤ vertices → (K → List Bool) → K → List Bool
  | 0, _, base => counter placement base 0
  | r + 1, bounded, base =>
      finalTapes graph n placement output r (by omega)
        (PoweringMachineVertex.finalTapes graph n placement output ⟨r, by omega⟩
          (counter placement base r))

def steps (graph : PortTables.Table vertices d) (n : Nat) :
    (remaining : Nat) → remaining ≤ vertices → Nat
  | 0, _ => 1
  | r + 1, bounded =>
      2 + PoweringMachineVertex.steps graph ⟨r, by omega⟩ n + steps graph n r (by omega)

theorem steps_le (graph : PortTables.Table vertices d) (n remaining : Nat)
    (bounded : remaining ≤ vertices) :
    steps graph n remaining bounded ≤
      remaining * (PoweringMachineVertex.budget d n (PortTables.tableBits graph).length + 2) + 1 := by
  induction remaining with
  | zero => simp [steps]
  | succ r ih =>
      have hv := PoweringMachineVertex.steps_le graph (⟨r, by omega⟩ : Fin vertices) n
      have hi := ih (by omega)
      simp only [steps, Nat.add_mul, Nat.one_mul]
      omega

theorem finalTapes_ready (graph : PortTables.Table vertices d) (n : Nat)
    (placement : Placement K n) (distinct : Function.Injective placement)
    (output : K) (outside : ∀ i, output ≠ placement i)
    (remaining : Nat) (bounded : remaining ≤ vertices) (base : K → List Bool)
    (ready : Ready graph n placement base) :
    Ready graph n placement (finalTapes graph n placement output remaining bounded base) := by
  induction remaining generalizing base with
  | zero =>
      constructor
      · rw [finalTapes, counter_other placement distinct base 0 0 (by decide)]
        exact ready.table
      · rw [finalTapes, counter_other placement distinct base 0 5 (by decide)]
        exact ready.scratch
      · rw [finalTapes, counter_other placement distinct base 0 8 (by decide)]
        exact ready.leftCopy
      · rw [finalTapes, counter_other placement distinct base 0 9 (by decide)]
        exact ready.rightCopy
      · rw [finalTapes, counter_other placement distinct base 0 10 (by decide)]
        exact ready.data
  | succ r ih =>
      apply ih
      apply ready_of_vertex graph n placement _ (⟨r, by omega⟩ : Fin vertices)
      exact PoweringMachineVertex.finalTapes_ready graph n placement distinct output outside
        ⟨r, by omega⟩ _ [] (ready_vertex graph n placement distinct base ready _)

def prefixRows (graph : PortTables.Table vertices d) (n : Nat) : Nat → List Bool
  | 0 => []
  | r + 1 => prefixRows graph n r ++
      if h : r < vertices then PoweringTableLayout.vertexRowBits graph n ⟨r, h⟩ else []

theorem prefixRows_ofFn (graph : PortTables.Table vertices d) (n remaining : Nat)
    (bounded : remaining ≤ vertices) :
    prefixRows graph n remaining =
      (List.ofFn (fun i : Fin remaining =>
        PoweringTableLayout.vertexRowBits graph n (Fin.castLE bounded i))).flatten := by
  induction remaining with
  | zero => rfl
  | succ r ih =>
      have hr : r < vertices := by omega
      rw [prefixRows, dite_eq_left hr, List.ofFn_succ_last, List.flatten_append]
      simp only [List.flatten_cons, List.flatten_nil, List.append_nil]
      change prefixRows graph n r ++ PoweringTableLayout.vertexRowBits graph n ⟨r, hr⟩ =
        (List.ofFn (fun i : Fin r => PoweringTableLayout.vertexRowBits graph n
          (Fin.castLE (show r ≤ vertices by omega) i))).flatten ++
          PoweringTableLayout.vertexRowBits graph n ⟨r, hr⟩
      rw [ih]

theorem prefixRows_all (graph : PortTables.Table vertices d) (n : Nat) :
    prefixRows graph n vertices =
      (List.finRange vertices).flatMap (PoweringTableLayout.vertexRowBits graph n) := by
  rw [prefixRows_ofFn graph n vertices (Nat.le_refl _)]
  simp only [List.finRange, List.flatMap_def, List.map_ofFn]
  rfl

theorem finalTapes_output (graph : PortTables.Table vertices d) (n : Nat)
    (placement : Placement K n) (distinct : Function.Injective placement)
    (output : K) (outside : ∀ i, output ≠ placement i)
    (remaining : Nat) (bounded : remaining ≤ vertices) (base : K → List Bool)
    (ready : Ready graph n placement base) :
    finalTapes graph n placement output remaining bounded base output =
      prefixRows graph n remaining ++ base output := by
  induction remaining generalizing base with
  | zero =>
      exact MachineUnaryCounter.counterTapes_other (placement (.inl 1)) output (outside _)
        base 0 []
  | succ r ih =>
      let vertex : Fin vertices := ⟨r, by omega⟩
      let current := counter placement base r
      have vertexReady := ready_vertex graph n placement distinct base ready vertex
      have nextReady := PoweringMachineVertex.finalTapes_ready graph n placement distinct
        output outside vertex current [] vertexReady
      change finalTapes graph n placement output r (by omega)
        (PoweringMachineVertex.finalTapes graph n placement output vertex current) output = _
      rw [ih (by omega) _ (ready_of_vertex graph n placement _ vertex nextReady),
        PoweringMachineVertex.finalTapes_output graph n placement distinct output outside
          vertex current [] vertexReady]
      have hc : current output = base output :=
        MachineUnaryCounter.counterTapes_other (placement (.inl 1)) output (outside _) base r []
      rw [hc, prefixRows, dite_eq_left vertex.isLt, List.append_assoc]

theorem finalTapes_other (graph : PortTables.Table vertices d) (n : Nat)
    (placement : Placement K n) (output : K) (remaining : Nat)
    (bounded : remaining ≤ vertices) (base : K → List Bool)
    (k : K) (hout : k ≠ output) (outside : ∀ i, k ≠ placement i) :
    finalTapes graph n placement output remaining bounded base k = base k := by
  induction remaining generalizing base with
  | zero => exact MachineUnaryCounter.counterTapes_other _ _ (outside _) base 0 []
  | succ r ih =>
      rw [finalTapes, ih, PoweringMachineVertex.finalTapes_other graph n placement output
        ⟨r, by omega⟩ _ k hout outside]
      exact MachineUnaryCounter.counterTapes_other _ _ (outside _) base r []

theorem loopTrace (graph : PortTables.Table vertices d) (n : Nat)
    (placement : Placement K n) (distinct : Function.Injective placement)
    (output : K) (outside : ∀ i, output ≠ placement i)
    (guardLabel bridgeLabel exitLabel : Λ) (labels : PoweringMachineVertex.Label d n → Λ)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ (State d n))
    (atGuard : program guardLabel =
      MachineUnaryCounter.guard (placement (.inl 1)) bridgeLabel exitLabel)
    (atBridge : program bridgeLabel = bridge d n labels guardLabel)
    (atVertex : ∀ l, program (labels l) =
      PoweringMachineVertex.instruction n placement output labels (some guardLabel) l)
    (remaining : Nat) (bounded : remaining ≤ vertices) (base : K → List Bool)
    (ready : Ready graph n placement base) :
    (advance (TM2.step program))^[steps graph n remaining bounded]
      (some ⟨some guardLabel, PoweringMasterState.clean (PoweringMachineRowBody.bufferSize d n),
        counter placement base remaining⟩) =
      some ⟨some exitLabel, PoweringMasterState.clean (PoweringMachineRowBody.bufferSize d n),
        finalTapes graph n placement output remaining bounded base⟩ := by
  let initial := PoweringMasterState.clean (PoweringMachineRowBody.bufferSize d n)
  induction remaining generalizing base with
  | zero =>
      simpa only [steps, finalTapes, counter, initial, PoweringMasterState.clean,
        PoweringMasterState.withBuffer] using
        MachineUnaryCounter.guardTrace_zero (placement (.inl 1)) guardLabel bridgeLabel exitLabel
          program atGuard base [] initial.1 none
  | succ r ih =>
      let vertex : Fin vertices := ⟨r, by omega⟩
      let current := counter placement base r
      let next := PoweringMachineVertex.finalTapes graph n placement output vertex current
      have vertexReady : PoweringMachineRowBody.Ready graph n placement vertex [] current :=
        ready_vertex graph n placement distinct base ready vertex
      have nextVertexReady := PoweringMachineVertex.finalTapes_ready graph n placement distinct
        output outside vertex current [] vertexReady
      have nextReady : Ready graph n placement next :=
        ready_of_vertex graph n placement next vertex nextVertexReady
      have sameCounter : counter placement next r = next := by
        have hs := nextVertexReady.1.source
        change next (placement (.inl 1)) = encodeWord r ++ [] at hs
        unfold counter MachineUnaryCounter.counterTapes
        rw [← hs]
        exact Function.update_eq_self _ _
      have tailRun := ih (by omega) next nextReady
      rw [sameCounter] at tailRun
      have guardRun : advance (TM2.step program)
          (some ⟨some guardLabel, initial, counter placement base (r + 1)⟩) =
          some ⟨some bridgeLabel, initial, current⟩ := by
        simpa only [advance_some, current, counter, initial, PoweringMasterState.clean,
          PoweringMasterState.withBuffer] using
          MachineUnaryCounter.guardStep_succ (placement (.inl 1)) guardLabel bridgeLabel exitLabel
            program atGuard base r [] initial.1 none
      have bridgeRun : advance (TM2.step program)
          (some ⟨some bridgeLabel, initial, current⟩) =
          some ⟨PoweringMachineVertex.entry d n labels (some guardLabel), initial, current⟩ := by
        change some (TM2.stepAux (program bridgeLabel) initial current) = _
        rw [atBridge, vertexEntry]
        rfl
      have vertexRun := PoweringMachineVertex.vertexTrace graph n placement distinct output outside
        vertex labels (some guardLabel) program atVertex current [] vertexReady
      change (advance (TM2.step program))^[2 + PoweringMachineVertex.steps graph vertex n +
          steps graph n r (by omega)]
        (some ⟨some guardLabel, initial, counter placement base (r + 1)⟩) = _
      rw [show 2 + PoweringMachineVertex.steps graph vertex n + steps graph n r (by omega) =
          (steps graph n r (by omega) + PoweringMachineVertex.steps graph vertex n) + 1 + 1 by omega,
        Function.iterate_succ_apply, guardRun, Function.iterate_succ_apply, bridgeRun,
        Function.iterate_add_apply, vertexRun]
      exact tailRun

def loopInTime (graph : PortTables.Table vertices d) (n : Nat)
    (placement : Placement K n) (distinct : Function.Injective placement)
    (output : K) (outside : ∀ i, output ≠ placement i)
    (guardLabel bridgeLabel exitLabel : Λ) (labels : PoweringMachineVertex.Label d n → Λ)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ (State d n))
    (atGuard : program guardLabel =
      MachineUnaryCounter.guard (placement (.inl 1)) bridgeLabel exitLabel)
    (atBridge : program bridgeLabel = bridge d n labels guardLabel)
    (atVertex : ∀ l, program (labels l) =
      PoweringMachineVertex.instruction n placement output labels (some guardLabel) l)
    (remaining : Nat) (bounded : remaining ≤ vertices) (base : K → List Bool)
    (ready : Ready graph n placement base) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some guardLabel, PoweringMasterState.clean (PoweringMachineRowBody.bufferSize d n),
        counter placement base remaining⟩
      (some ⟨some exitLabel, PoweringMasterState.clean (PoweringMachineRowBody.bufferSize d n),
        finalTapes graph n placement output remaining bounded base⟩)
      (remaining * (PoweringMachineVertex.budget d n (PortTables.tableBits graph).length + 2) + 1) where
  steps := steps graph n remaining bounded
  evals_in_steps := loopTrace graph n placement distinct output outside guardLabel bridgeLabel
    exitLabel labels program atGuard atBridge atVertex remaining bounded base ready
  steps_le_m := steps_le graph n remaining bounded

end DFVSGames.Foundations.Complexity.PoweringMachineOuterLoop
end

section

namespace DFVSGames.Foundations.Complexity.PoweringMachineFinish

open Turing MachineComposition

variable {K Λ σ : Type} [DecidableEq K] {N : Nat}

abbrev Alphabet (_ : K) := Bool

abbrev Label (enumeration : Fin N ≃ K) (output : K) :=
  MachineUnaryAffineAt.Label ⊕ (MachineUnaryAffineAt.Label ⊕
    MachineDrainMany.Label (MachineDrainMany.workTapes enumeration output))

def copyInstruction (source scratch output : K)
    (labels : MachineUnaryAffineAt.Label → Λ) (exit : Option Λ) :
    MachineUnaryAffineAt.Label → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool)
  | .seed => MachineUnaryAffineAt.seed output 0 (labels .scan)
  | .scan => MachineUnaryAffineAt.scan source scratch output 1 (labels .scan) (labels .restore)
  | .restore => Reduction.MachineTransfer.loopAt scratch source id false (labels .restore) exit

def instruction (enumeration : Fin N ≃ K) (headerV headerD output scratch : K)
    (labels : Label enumeration output → Λ) :
    Label enumeration output → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool)
  | .inl l => copyInstruction headerD scratch output (fun q => labels (.inl q))
      (some (labels (.inr (.inl .seed)))) l
  | .inr (.inl l) => copyInstruction headerV scratch output
      (fun q => labels (.inr (.inl q)))
      (MachineDrainMany.entry (MachineDrainMany.workTapes enumeration output)
        (fun q => labels (.inr (.inr q))) none) l
  | .inr (.inr l) => MachineDrainMany.instruction
      (MachineDrainMany.workTapes enumeration output) (fun q => labels (.inr (.inr q))) none l

def program (enumeration : Fin N ≃ K) (headerV headerD output scratch : K) :
    Label enumeration output →
      TM2.Stmt (Alphabet (K := K)) (Label enumeration output) (σ × Option Bool) :=
  instruction enumeration headerV headerD output scratch id

def afterD (output : K) (base : K → List Bool) (m : Nat) : K → List Bool :=
  Function.update base output (encodeWord m ++ base output)

def afterHeaders (output : K) (base : K → List Bool) (n m : Nat) : K → List Bool :=
  Function.update base output (encodeWords [n, m] ++ base output)

@[simp] theorem afterHeaders_output (output : K) (base : K → List Bool) (n m : Nat) :
    afterHeaders output base n m output = encodeWords [n, m] ++ base output := by
  simp only [afterHeaders, Function.update_self]

theorem afterHeaders_other (output : K) (base : K → List Bool) (n m : Nat)
    (k : K) (hk : k ≠ output) : afterHeaders output base n m k = base k :=
  Function.update_of_ne hk _ _

def copySteps (n m : Nat) : Nat := (2 * (m + 1) + 1) + (2 * (n + 1) + 1)

theorem copySteps_eq (n m : Nat) : copySteps n m = 2 * (n + m) + 6 := by
  unfold copySteps
  omega

def steps (enumeration : Fin N ≃ K) (output : K) (base : K → List Bool) (n m : Nat) : Nat :=
  copySteps n m + MachineDrainMany.steps (MachineDrainMany.workTapes enumeration output)
    (afterHeaders output base n m)

def budget (enumeration : Fin N ≃ K) (output : K) (base : K → List Bool) (n m : Nat) : Nat :=
  copySteps n m + (MachineDrainMany.lengthSum (MachineDrainMany.workTapes enumeration output)
    (afterHeaders output base n m) + (MachineDrainMany.workTapes enumeration output).length)

private theorem trace_trans_inline_PoweringMachineFinish {α : Type*} (f : α → α) {a b : Nat} {x y z : α}
    (first : f^[a] x = y) (second : f^[b] y = z) : f^[a + b] x = z := by
  rw [Nat.add_comm, Function.iterate_add_apply, first, second]

theorem traceAt (enumeration : Fin N ≃ K) (headerV headerD output scratch : K)
    (hvs : headerV ≠ scratch) (hvo : headerV ≠ output)
    (hds : headerD ≠ scratch) (hdo : headerD ≠ output) (hso : scratch ≠ output)
    (labels : Label enumeration output → Λ)
    (target : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atLabels : ∀ l, target (labels l) =
      instruction enumeration headerV headerD output scratch labels l)
    (base : K → List Bool) (n m : Nat) (suffixV suffixD : List Bool)
    (wordV : base headerV = encodeWord n ++ suffixV)
    (wordD : base headerD = encodeWord m ++ suffixD)
    (scratchEmpty : base scratch = []) (ambient : σ) (register : Option Bool) :
    (advance (TM2.step target))^[steps enumeration output base n m]
      (some ⟨some (labels (.inl .seed)), (ambient, register), base⟩) =
      some ⟨none, (ambient, none),
        MachineDrainMany.haltTapes output (encodeWords [n, m] ++ base output)⟩ := by
  have hd := MachineUnaryAffineAt.seededAffineTrace headerD scratch output hds hdo hso 1 0
    (labels (.inl .seed)) (labels (.inl .scan)) (labels (.inl .restore))
    (some (labels (.inr (.inl .seed)))) target
    (atLabels (.inl .seed)) (atLabels (.inl .scan)) (atLabels (.inl .restore))
    base m suffixD wordD scratchEmpty ambient register
  simp only [Nat.one_mul, Nat.add_zero] at hd
  change (advance (TM2.step target))^[2 * (m + 1) + 1]
    (some ⟨some (labels (.inl .seed)), (ambient, register), base⟩) =
    some ⟨some (labels (.inr (.inl .seed))), (ambient, none), afterD output base m⟩ at hd
  have wordV' : afterD output base m headerV = encodeWord n ++ suffixV := by
    simpa only [afterD, Function.update_of_ne hvo] using wordV
  have scratchEmpty' : afterD output base m scratch = [] := by
    simpa only [afterD, Function.update_of_ne hso] using scratchEmpty
  have hv := MachineUnaryAffineAt.seededAffineTrace headerV scratch output hvs hvo hso 1 0
    (labels (.inr (.inl .seed))) (labels (.inr (.inl .scan)))
    (labels (.inr (.inl .restore)))
    (MachineDrainMany.entry (MachineDrainMany.workTapes enumeration output)
      (fun q => labels (.inr (.inr q))) none)
    target (atLabels (.inr (.inl .seed))) (atLabels (.inr (.inl .scan)))
    (atLabels (.inr (.inl .restore))) (afterD output base m) n suffixV
    wordV' scratchEmpty' ambient none
  simp only [Nat.one_mul, Nat.add_zero] at hv
  have copied : Function.update (afterD output base m) output
      (encodeWord n ++ afterD output base m output) = afterHeaders output base n m := by
    simp only [afterD, afterHeaders, Function.update_self, Function.update_idem,
      encodeWords, List.append_nil, List.append_assoc]
  rw [copied] at hv
  have cleaned := MachineDrainMany.cleanupTrace enumeration output
    (fun q => labels (.inr (.inr q))) target (fun l => atLabels (.inr (.inr l)))
    (afterHeaders output base n m) ambient
  rw [afterHeaders_output] at cleaned
  have total := trace_trans_inline_PoweringMachineFinish _ (trace_trans_inline_PoweringMachineFinish _ hd hv) cleaned
  simpa only [steps, copySteps] using total

theorem trace (enumeration : Fin N ≃ K) (headerV headerD output scratch : K)
    (hvs : headerV ≠ scratch) (hvo : headerV ≠ output)
    (hds : headerD ≠ scratch) (hdo : headerD ≠ output) (hso : scratch ≠ output)
    (base : K → List Bool) (n m : Nat) (suffixV suffixD : List Bool)
    (wordV : base headerV = encodeWord n ++ suffixV)
    (wordD : base headerD = encodeWord m ++ suffixD)
    (scratchEmpty : base scratch = []) (ambient : σ) (register : Option Bool) :
    (advance (TM2.step (program enumeration headerV headerD output scratch)))^[
      steps enumeration output base n m]
      (some ⟨some (.inl .seed), (ambient, register), base⟩) =
      some ⟨none, (ambient, none),
        MachineDrainMany.haltTapes output (encodeWords [n, m] ++ base output)⟩ :=
  traceAt enumeration headerV headerD output scratch hvs hvo hds hdo hso id
    (program enumeration headerV headerD output scratch) (fun _ => rfl)
    base n m suffixV suffixD wordV wordD scratchEmpty ambient register

theorem steps_le_budget (enumeration : Fin N ≃ K) (output : K)
    (base : K → List Bool) (n m : Nat) :
    steps enumeration output base n m ≤ budget enumeration output base n m :=
  Nat.add_le_add_left (MachineDrainMany.steps_le
    (MachineDrainMany.workTapes enumeration output) (afterHeaders output base n m)) _

theorem afterHeaders_length_le (output : K) (base : K → List Bool) (n m bound : Nat)
    (bounded : ∀ k, (base k).length ≤ bound) (k : K) :
    (afterHeaders output base n m k).length ≤ bound + n + m + 2 := by
  by_cases hk : k = output
  · subst k
    rw [afterHeaders_output]
    have hb := bounded output
    simp only [List.length_append, encodeWords, encodeWord_length, List.length_nil]
    omega
  · rw [afterHeaders_other output base n m k hk]
    have hb := bounded k
    omega

theorem steps_le_uniform (enumeration : Fin N ≃ K) (output : K)
    (base : K → List Bool) (n m bound : Nat)
    (bounded : ∀ k, (base k).length ≤ bound) :
    steps enumeration output base n m ≤ 2 * (n + m) + 6 + N * (bound + n + m + 3) := by
  have hc := MachineDrainMany.steps_le_uniform (MachineDrainMany.workTapes enumeration output)
    (afterHeaders output base n m) (bound + n + m + 2)
    (afterHeaders_length_le output base n m bound bounded)
  have hl := MachineDrainMany.workTapes_length_le enumeration output
  have hm := Nat.mul_le_mul_right (bound + n + m + 3) hl
  rw [show bound + n + m + 2 + 1 = bound + n + m + 3 by omega] at hc
  unfold steps
  rw [copySteps_eq]
  exact Nat.add_le_add_left (hc.trans hm) _

def execution (enumeration : Fin N ≃ K) (headerV headerD output scratch : K)
    (hvs : headerV ≠ scratch) (hvo : headerV ≠ output)
    (hds : headerD ≠ scratch) (hdo : headerD ≠ output) (hso : scratch ≠ output)
    (base : K → List Bool) (n m : Nat) (suffixV suffixD : List Bool)
    (wordV : base headerV = encodeWord n ++ suffixV)
    (wordD : base headerD = encodeWord m ++ suffixD)
    (scratchEmpty : base scratch = []) (ambient : σ) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step (program enumeration headerV headerD output scratch))
      ⟨some (.inl .seed), (ambient, register), base⟩
      (some ⟨none, (ambient, none),
        MachineDrainMany.haltTapes output (encodeWords [n, m] ++ base output)⟩)
      (budget enumeration output base n m) where
  steps := steps enumeration output base n m
  evals_in_steps := trace enumeration headerV headerD output scratch hvs hvo hds hdo hso
    base n m suffixV suffixD wordV wordD scratchEmpty ambient register
  steps_le_m := steps_le_budget enumeration output base n m

end DFVSGames.Foundations.Complexity.PoweringMachineFinish
end

section

namespace DFVSGames.Foundations.Complexity.PoweringMachineGlobal

open Turing

abbrev Tape (n : Nat) :=
  PoweringMachineInitialize.GlobalTape (PoweringMachineRowBody.capacity n)

abbrev State (d n : Nat) :=
  PoweringMasterState.Master (PoweringMachineRowBody.bufferSize d n)

def placement (n : Nat) :
    PoweringMachineTapes.Tape (PoweringMachineRowBody.capacity n) → Tape n :=
  PoweringMachineInitialize.commonPlacement (PoweringMachineRowBody.capacity n)

def inputTape (n : Nat) : Tape n :=
  placement n (PoweringMachineTapes.table (PoweringMachineRowBody.capacity n))

def outputTape (n : Nat) : Tape n :=
  PoweringMachineInitialize.finalOutput (PoweringMachineRowBody.capacity n)

def headerVertices (n : Nat) : Tape n := .inl PoweringMachineLoop.HeaderTape.vertices
def headerDarts (n : Nat) : Tape n := .inl PoweringMachineLoop.HeaderTape.darts

def enumeration (n : Nat) :
    Fin (4 + (11 + PoweringMachineRowBody.capacity n + 1)) ≃ Tape n :=
  PoweringGlobalEnumeration.enumeration (PoweringMachineRowBody.capacity n)

abbrev FinishLabel (n : Nat) := PoweringMachineFinish.Label (enumeration n) (outputTape n)

abbrev Label (d n : Nat) := PoweringMachineInitialize.Label ⊕
  (Bool ⊕ (PoweringMachineVertex.Label d n ⊕ FinishLabel n))

instance labelFintype (d n : Nat) : Fintype (Label d n) :=
  inferInstanceAs (Fintype (PoweringMachineInitialize.Label ⊕
    (Bool ⊕ (PoweringMachineVertex.Label d n ⊕ FinishLabel n))))

def initLabels (d n : Nat) : PoweringMachineInitialize.Label → Label d n := Sum.inl
def guardLabel (d n : Nat) : Label d n := .inr (.inl false)
def bridgeLabel (d n : Nat) : Label d n := .inr (.inl true)

def vertexLabels (d n : Nat) (label : PoweringMachineVertex.Label d n) : Label d n :=
  .inr (.inr (.inl label))

def finishLabels (d n : Nat) (label : FinishLabel n) : Label d n :=
  .inr (.inr (.inr label))

def finishEntry (d n : Nat) : Label d n := finishLabels d n (.inl .seed)

def main (d n : Nat) : Label d n := initLabels d n (.inr .seed)

def program (d n : Nat) :
    Label d n → TM2.Stmt (fun _ : Tape n => Bool) (Label d n) (State d n)
  | .inl label => PoweringMachineInitialize.instruction
      (PoweringMachineRowBody.capacity n) (PoweringMachineRowBody.bufferSize d n)
      (PCP.PoweringTableLayout.blockSize d n) (initLabels d n) (some (guardLabel d n)) label
  | .inr (.inl false) => MachineUnaryCounter.guard
      (placement n (PoweringMachineTapes.start (PoweringMachineRowBody.capacity n)))
      (bridgeLabel d n) (finishEntry d n)
  | .inr (.inl true) => PoweringMachineOuterLoop.bridge d n (vertexLabels d n) (guardLabel d n)
  | .inr (.inr (.inl label)) => PoweringMachineVertex.instruction n (placement n) (outputTape n)
      (vertexLabels d n) (some (guardLabel d n)) label
  | .inr (.inr (.inr label)) => PoweringMachineFinish.instruction (enumeration n)
      (headerVertices n) (headerDarts n) (outputTape n)
      (placement n (PoweringMachineTapes.scratch (PoweringMachineRowBody.capacity n)))
      (finishLabels d n) label

@[simp] theorem atInit (d n : Nat) (label : PoweringMachineInitialize.Label) :
    program d n (initLabels d n label) = PoweringMachineInitialize.instruction
      (PoweringMachineRowBody.capacity n) (PoweringMachineRowBody.bufferSize d n)
      (PCP.PoweringTableLayout.blockSize d n) (initLabels d n) (some (guardLabel d n)) label := rfl

@[simp] theorem atGuard (d n : Nat) :
    program d n (guardLabel d n) = MachineUnaryCounter.guard
      (placement n (PoweringMachineTapes.start (PoweringMachineRowBody.capacity n)))
      (bridgeLabel d n) (finishEntry d n) := rfl

@[simp] theorem atBridge (d n : Nat) :
    program d n (bridgeLabel d n) =
      PoweringMachineOuterLoop.bridge d n (vertexLabels d n) (guardLabel d n) := rfl

@[simp] theorem atVertex (d n : Nat) (label : PoweringMachineVertex.Label d n) :
    program d n (vertexLabels d n label) = PoweringMachineVertex.instruction n
      (placement n) (outputTape n) (vertexLabels d n) (some (guardLabel d n)) label := rfl

@[simp] theorem atFinish (d n : Nat) (label : FinishLabel n) :
    program d n (finishLabels d n label) = PoweringMachineFinish.instruction (enumeration n)
      (headerVertices n) (headerDarts n) (outputTape n)
      (placement n (PoweringMachineTapes.scratch (PoweringMachineRowBody.capacity n)))
      (finishLabels d n) label := rfl

def machine (d n : Nat) : FinTM2 where
  K := Tape n
  k₀ := inputTape n
  k₁ := outputTape n
  Γ _ := Bool
  Λ := Label d n
  main := main d n
  σ := State d n
  initialState := PoweringMasterState.clean (PoweringMachineRowBody.bufferSize d n)
  m := program d n

@[simp] theorem machine_code (d n : Nat) (label : Label d n) :
    (machine d n).m label = program d n label := rfl

@[simp] theorem machine_main (d n : Nat) : (machine d n).main = main d n := rfl

@[simp] theorem machine_initialState (d n : Nat) :
    (machine d n).initialState = PoweringMasterState.clean (PoweringMachineRowBody.bufferSize d n) := rfl

theorem input_ne_output (n : Nat) : inputTape n ≠ outputTape n :=
  PoweringMachineInitialize.commonPlacement_ne_finalOutput (PoweringMachineRowBody.capacity n)
    (PoweringMachineTapes.table (PoweringMachineRowBody.capacity n))

end DFVSGames.Foundations.Complexity.PoweringMachineGlobal
end

section

namespace DFVSGames.Foundations.Complexity.PoweringInitializeFrame

open Turing PCP

variable {vertices d : Nat}

def initialExtra (graph : PortTables.Table vertices d) (n : Nat) :
    PoweringMachineInitialize.ExtraTape (PoweringMachineRowBody.capacity n) → List Bool :=
  fun tape => if tape = .inl (PoweringMachineTapes.table (PoweringMachineRowBody.capacity n))
    then PortTables.tableBits graph else []

@[simp] theorem initialExtra_table (graph : PortTables.Table vertices d) (n : Nat) :
    initialExtra graph n (.inl (PoweringMachineTapes.table (PoweringMachineRowBody.capacity n))) =
      PortTables.tableBits graph := by simp [initialExtra]

theorem initialExtra_other (graph : PortTables.Table vertices d) (n : Nat)
    (tape : PoweringMachineInitialize.ExtraTape (PoweringMachineRowBody.capacity n))
    (hne : tape ≠ .inl (PoweringMachineTapes.table (PoweringMachineRowBody.capacity n))) :
    initialExtra graph n tape = [] := by simp [initialExtra, hne]

@[simp] theorem initialExtra_scratch (graph : PortTables.Table vertices d) (n : Nat) :
    initialExtra graph n
      (.inl (PoweringMachineTapes.scratch (PoweringMachineRowBody.capacity n))) = [] := by
  simp [initialExtra, PoweringMachineTapes.table, PoweringMachineTapes.scratch]

def preparedTapes (graph : PortTables.Table vertices d) (n : Nat) :
    PoweringMachineGlobal.Tape n → List Bool :=
  PoweringMachineInitialize.mergeTapes
    (PoweringMachineLoop.finalTapes (PoweringTableLayout.blockSize d n) vertices [])
    (initialExtra graph n)

theorem prepared_commonRole (graph : PortTables.Table vertices d) (n : Nat)
    (j : Fin 11) (hne : j ≠ 1) :
    preparedTapes graph n (PoweringMachineGlobal.placement n (.inl j)) =
      if j = 0 then PortTables.tableBits graph else [] := by
  simp [preparedTapes, PoweringMachineGlobal.placement,
    PoweringMachineInitialize.commonPlacement, PoweringMachineTapes.start,
    PoweringMachineInitialize.mergeTapes, initialExtra, PoweringMachineTapes.table, hne]

theorem prepared_ready (graph : PortTables.Table vertices d) (n : Nat) :
    PoweringMachineOuterLoop.Ready graph n (PoweringMachineGlobal.placement n)
      (preparedTapes graph n) := by
  constructor
  · simpa using prepared_commonRole graph n 0 (by decide)
  · simpa using prepared_commonRole graph n 5 (by decide)
  · simpa using prepared_commonRole graph n 8 (by decide)
  · simpa using prepared_commonRole graph n 9 (by decide)
  · simpa using prepared_commonRole graph n 10 (by decide)

@[simp] theorem prepared_start (graph : PortTables.Table vertices d) (n : Nat) :
    preparedTapes graph n (PoweringMachineGlobal.placement n (.inl 1)) =
      encodeWord vertices := by
  simpa only [preparedTapes, PoweringMachineGlobal.placement, PoweringMachineTapes.start] using
    PoweringMachineInitialize.final_counter (PoweringMachineRowBody.capacity n)
      (PoweringTableLayout.blockSize d n) vertices (initialExtra graph n)

theorem prepared_counter (graph : PortTables.Table vertices d) (n : Nat) :
    PoweringMachineOuterLoop.counter (PoweringMachineGlobal.placement n)
      (preparedTapes graph n) vertices = preparedTapes graph n := by
  unfold PoweringMachineOuterLoop.counter MachineUnaryCounter.counterTapes
  rw [List.append_nil, ← prepared_start graph n]
  simp only [Function.update_eq_self]

@[simp] theorem prepared_output (graph : PortTables.Table vertices d) (n : Nat) :
    preparedTapes graph n (PoweringMachineGlobal.outputTape n) = [] := by
  simp [preparedTapes, PoweringMachineGlobal.outputTape, PoweringMachineInitialize.finalOutput,
    PoweringMachineInitialize.mergeTapes, initialExtra]

@[simp] theorem prepared_vertices (graph : PortTables.Table vertices d) (n : Nat) :
    preparedTapes graph n (PoweringMachineGlobal.headerVertices n) = encodeWord vertices := rfl

@[simp] theorem prepared_darts (graph : PortTables.Table vertices d) (n : Nat) :
    preparedTapes graph n (PoweringMachineGlobal.headerDarts n) =
      encodeWord (PoweringTableLayout.blockSize d n * vertices) := rfl

@[simp] theorem prepared_source (graph : PortTables.Table vertices d) (n : Nat) :
    preparedTapes graph n (.inl PoweringMachineLoop.HeaderTape.source) = [] := rfl

def preparedCfg (graph : PortTables.Table vertices d) (n : Nat) :
    (PoweringMachineGlobal.machine d n).Cfg :=
  ⟨some (PoweringMachineGlobal.guardLabel d n),
    PoweringMasterState.clean (PoweringMachineRowBody.bufferSize d n), preparedTapes graph n⟩

theorem initialGlobalTapes_eq (graph : PortTables.Table vertices d) (n : Nat) :
    PoweringMachineInitialize.initialGlobalTapes (initialExtra graph n) =
      fun tape => if tape = PoweringMachineGlobal.inputTape n
        then PortTables.tableBits graph else [] := by
  funext tape
  cases tape with
  | inl field =>
    simp [PoweringMachineInitialize.initialGlobalTapes, PoweringMachineInitialize.mergeTapes,
      PoweringMachineGlobal.inputTape, PoweringMachineGlobal.placement,
      PoweringMachineInitialize.commonPlacement_table]
  | inr field =>
    simp [PoweringMachineInitialize.initialGlobalTapes, PoweringMachineInitialize.mergeTapes,
      PoweringMachineGlobal.inputTape, PoweringMachineGlobal.placement,
      PoweringMachineInitialize.commonPlacement_table, initialExtra]

private theorem machine_initialStacks_inline_PoweringInitializeFrame (d n : Nat) (input : List Bool) :
    (initList (PoweringMachineGlobal.machine d n) input).stk =
      fun tape => if tape = PoweringMachineGlobal.inputTape n then input else [] := by
  funext tape
  dsimp only [initList, PoweringMachineGlobal.machine]
  split <;> simp_all

theorem initList_eq (graph : PortTables.Table vertices d) (n : Nat) :
    initList (PoweringMachineGlobal.machine d n) (PortTables.tableBits graph) =
      ⟨some (PoweringMachineGlobal.main d n),
        PoweringMasterState.clean (PoweringMachineRowBody.bufferSize d n),
        PoweringMachineInitialize.initialGlobalTapes (initialExtra graph n)⟩ := by
  have ht := (machine_initialStacks_inline_PoweringInitializeFrame d n (PortTables.tableBits graph)).trans
    (initialGlobalTapes_eq graph n).symm
  exact congrArg (TM2.Cfg.mk _ _) ht

theorem tableBits_head (graph : PortTables.Table vertices d) :
    PortTables.tableBits graph = encodeWord vertices ++
      encodeWords (PortTables.tableWords graph).tail := rfl

def initializeInTime (graph : PortTables.Table vertices d) (n : Nat) :
    StateTransition.EvalsToInTime (PoweringMachineGlobal.machine d n).step
      (initList (PoweringMachineGlobal.machine d n) (PortTables.tableBits graph))
      (some (preparedCfg graph n)) (3 * vertices + 5) := by
  rw [initList_eq]
  exact PoweringMachineInitialize.initializeAtInTime
    (PoweringMachineRowBody.capacity n) (PoweringMachineRowBody.bufferSize d n)
    (PoweringTableLayout.blockSize d n) vertices
    (PoweringMachineGlobal.initLabels d n) (some (PoweringMachineGlobal.guardLabel d n))
    (PoweringMachineGlobal.program d n) (PoweringMachineGlobal.atInit d n)
    (initialExtra graph n) (encodeWords (PortTables.tableWords graph).tail)
    (by rw [initialExtra_table, tableBits_head]) (initialExtra_scratch graph n)
    (PoweringMasterState.clean (PoweringMachineRowBody.bufferSize d n))

end DFVSGames.Foundations.Complexity.PoweringInitializeFrame
end

section

namespace DFVSGames.Foundations.Complexity.PoweringGlobalConfiguration

open Turing PoweringMachineGlobal

theorem placement_injective (n : Nat) : Function.Injective (placement n) :=
  PoweringMachineInitialize.commonPlacement_injective (PoweringMachineRowBody.capacity n)

theorem placement_ne_output (n : Nat)
    (tape : PoweringMachineTapes.Tape (PoweringMachineRowBody.capacity n)) :
    placement n tape ≠ outputTape n :=
  PoweringMachineInitialize.commonPlacement_ne_finalOutput
    (PoweringMachineRowBody.capacity n) tape

theorem output_ne_placement (n : Nat)
    (tape : PoweringMachineTapes.Tape (PoweringMachineRowBody.capacity n)) :
    outputTape n ≠ placement n tape := Ne.symm (placement_ne_output n tape)

theorem headerVertices_ne_placement (n : Nat)
    (tape : PoweringMachineTapes.Tape (PoweringMachineRowBody.capacity n)) :
    headerVertices n ≠ placement n tape :=
  Ne.symm (PoweringMachineInitialize.commonPlacement_ne_header
    (PoweringMachineRowBody.capacity n) tape .vertices (by decide))

theorem headerDarts_ne_placement (n : Nat)
    (tape : PoweringMachineTapes.Tape (PoweringMachineRowBody.capacity n)) :
    headerDarts n ≠ placement n tape :=
  Ne.symm (PoweringMachineInitialize.commonPlacement_ne_header
    (PoweringMachineRowBody.capacity n) tape .darts (by decide))

theorem placement_ne_headerVertices (n : Nat)
    (tape : PoweringMachineTapes.Tape (PoweringMachineRowBody.capacity n)) :
    placement n tape ≠ headerVertices n := Ne.symm (headerVertices_ne_placement n tape)

theorem placement_ne_headerDarts (n : Nat)
    (tape : PoweringMachineTapes.Tape (PoweringMachineRowBody.capacity n)) :
    placement n tape ≠ headerDarts n := Ne.symm (headerDarts_ne_placement n tape)

theorem headerVertices_ne_headerDarts (n : Nat) : headerVertices n ≠ headerDarts n := by
  simp [headerVertices, headerDarts]

theorem headerVertices_ne_output (n : Nat) : headerVertices n ≠ outputTape n := by
  simp [headerVertices, outputTape, PoweringMachineInitialize.finalOutput]

theorem headerDarts_ne_output (n : Nat) : headerDarts n ≠ outputTape n := by
  simp [headerDarts, outputTape, PoweringMachineInitialize.finalOutput]

theorem headerVertices_ne_scratch (n : Nat) :
    headerVertices n ≠
      placement n (PoweringMachineTapes.scratch (PoweringMachineRowBody.capacity n)) :=
  headerVertices_ne_placement n _

theorem headerDarts_ne_scratch (n : Nat) :
    headerDarts n ≠
      placement n (PoweringMachineTapes.scratch (PoweringMachineRowBody.capacity n)) :=
  headerDarts_ne_placement n _

theorem scratch_ne_output (n : Nat) :
    placement n (PoweringMachineTapes.scratch (PoweringMachineRowBody.capacity n)) ≠
      outputTape n :=
  placement_ne_output n _

@[simp] theorem boolList_mpr_eq (h : List Bool = List Bool) (bits : List Bool) :
    h.mpr bits = bits := rfl

theorem haltList_tapes (d n : Nat) (output : List Bool) :
    (Turing.haltList (machine d n) output).stk =
      MachineDrainMany.haltTapes (outputTape n) output := by
  funext tape
  dsimp only [Turing.haltList, machine, MachineDrainMany.haltTapes]
  split <;> simp_all

theorem haltList_eq (d n : Nat) (output : List Bool) :
    Turing.haltList (machine d n) output =
      (⟨none, PoweringMasterState.clean (PoweringMachineRowBody.bufferSize d n),
        MachineDrainMany.haltTapes (outputTape n) output⟩ : (machine d n).Cfg) := by
  change (⟨none, PoweringMasterState.clean (PoweringMachineRowBody.bufferSize d n),
      (Turing.haltList (machine d n) output).stk⟩ : (machine d n).Cfg) = _
  exact congrArg
    (fun tapes => (⟨none, PoweringMasterState.clean (PoweringMachineRowBody.bufferSize d n),
      tapes⟩ : (machine d n).Cfg)) (haltList_tapes d n output)

end DFVSGames.Foundations.Complexity.PoweringGlobalConfiguration
end

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
