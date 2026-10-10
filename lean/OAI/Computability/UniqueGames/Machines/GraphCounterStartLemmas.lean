import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.FinCases
import OAI.Computability.UniqueGames.Machines.GraphCounterFinish
import OAI.Computability.UniqueGames.Machines.GraphCounterModel
import OAI.Computability.UniqueGames.Machines.MachineCompositionLemmas
import OAI.Computability.UniqueGames.Machines.MachineControlLemmas
import OAI.Computability.UniqueGames.Machines.MachineCopy
import OAI.Computability.UniqueGames.Machines.MachineSubroutineLemmas
import OAI.Computability.UniqueGames.PCP.InputLemmas
import OAI.Computability.UniqueGames.Reduction.MachineSubstitution
import OAI.Computability.UniqueGames.Reduction.MachineTransfer

namespace OAI

/-! Actual archive-copy and unary-header addition before the embedded logarithm
machine. The two header values stay on tapes; they never enter finite control. -/

namespace UniqueGamesTheorem.Foundations.Complexity.GraphCounterModel

open Turing

def startExtra (input archive : List Bool) : ExtraTape → List Bool
  | .input => input
  | .archive => archive
  | _ => []

def startMemory (input archive sum : List Bool) : Tape → List Bool
  | .inl k => if k = 0 then sum else []
  | .inr k => startExtra input archive k

theorem startMemory_input_update (input archive sum replacement : List Bool) :
    Function.update (startMemory input archive sum) (.inr .input) replacement =
      startMemory replacement archive sum := by
  funext tape
  cases tape with
  | inl k => simp [startMemory]
  | inr k => cases k <;> simp [startMemory, startExtra]

theorem startMemory_sum_update (input archive sum replacement : List Bool) :
    Function.update (startMemory input archive sum) (.inl 0) replacement =
      startMemory input archive replacement := by
  funext tape
  cases tape with
  | inl k => by_cases h : k = 0 <;> simp [startMemory, h]
  | inr k => simp [startMemory]

theorem headerStep_zero (again next : Label)
    (atHeader : program again = readHeader again next)
    (suffix archive : List Bool) (sum : Nat)
    (state : MachineLogCounter.State) (register : Option Bool) :
    TM2.step program
      ⟨some again, (state, register), startMemory (encodeWord 0 ++ suffix) archive (encodeWord sum)⟩ =
      some ⟨some next, (state, none), startMemory suffix archive (encodeWord sum)⟩ := by
  change some (TM2.stepAux (program again) _ _) = _
  rw [atHeader]
  simp only [readHeader, TM2.stepAux, startMemory, startExtra, encodeWord,
    List.replicate_zero, List.nil_append, List.singleton_append, List.head?_cons,
    List.tail_cons, Option.getD_some, Bool.cond_false]
  rw [startMemory_input_update]

theorem headerStep_succ (again next : Label)
    (atHeader : program again = readHeader again next)
    (n sum : Nat) (suffix archive : List Bool)
    (state : MachineLogCounter.State) (register : Option Bool) :
    TM2.step program
      ⟨some again, (state, register),
        startMemory (encodeWord (n + 1) ++ suffix) archive (encodeWord sum)⟩ =
      some ⟨some again, (state, some true),
        startMemory (encodeWord n ++ suffix) archive (encodeWord (sum + 1))⟩ := by
  change some (TM2.stepAux (program again) _ _) = _
  rw [atHeader]
  simp only [readHeader, TM2.stepAux, startMemory, startExtra, encodeWord,
    List.replicate_succ, List.cons_append, List.head?_cons, List.tail_cons,
    Option.getD_some, Bool.cond_true]
  rw [startMemory_input_update, startMemory_sum_update]
  rfl

theorem headerTrace (again next : Label)
    (atHeader : program again = readHeader again next)
    (n sum : Nat) (suffix archive : List Bool)
    (state : MachineLogCounter.State) (register : Option Bool) :
    (MachineComposition.advance (TM2.step program))^[n + 1]
      (some ⟨some again, (state, register),
        startMemory (encodeWord n ++ suffix) archive (encodeWord sum)⟩) =
      some ⟨some next, (state, none), startMemory suffix archive (encodeWord (n + sum))⟩ := by
  induction n generalizing sum register with
  | zero =>
      simpa only [Nat.zero_add, Function.iterate_one, MachineComposition.advance_some] using
        headerStep_zero again next atHeader suffix archive sum state register
  | succ n ih =>
      rw [Function.iterate_succ_apply, MachineComposition.advance_some]
      rw [headerStep_succ again next atHeader n sum suffix archive state register]
      simpa only [Nat.add_assoc, Nat.add_comm 1 sum] using ih (sum + 1) (some true)

def headerInTime (again next : Label)
    (atHeader : program again = readHeader again next)
    (n sum : Nat) (suffix archive : List Bool)
    (state : MachineLogCounter.State) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some again, (state, register), startMemory (encodeWord n ++ suffix) archive (encodeWord sum)⟩
      (some ⟨some next, (state, none), startMemory suffix archive (encodeWord (n + sum))⟩)
      (n + 1) where
  steps := n + 1
  evals_in_steps := headerTrace again next atHeader n sum suffix archive state register
  steps_le_m := le_rfl

theorem initialMemory (word : List Bool) :
    initList machine word =
      ⟨some (.inr .copyFirst), initialState, startMemory word [] []⟩ := by
  have ht : (initList machine word).stk = startMemory word [] [] := by
    funext tape
    cases tape with
    | inl k => simp [initList, machine, startMemory]
    | inr k => cases k <;> simp [initList, machine, startMemory, startExtra]; rfl
  exact congrArg (TM2.Cfg.mk _ _) ht

theorem clockInitialMemory (word rest : List Bool) (sum : Nat) :
    clockConfiguration (startExtra rest word) none
      (initList MachineLogCounter.machine (encodeWord sum)) =
      ⟨some (.inl 0), initialState, startMemory rest word (encodeWord sum)⟩ := by
  have ht : clockTapes (initList MachineLogCounter.machine (encodeWord sum)).stk
      (startExtra rest word) = startMemory rest word (encodeWord sum) := by
    funext tape
    cases tape with
    | inl k =>
      fin_cases k <;> simp [clockTapes, initList, MachineLogCounter.machine, startMemory]; rfl
    | inr k => rfl
  exact congrArg (TM2.Cfg.mk _ _) ht

/-- Exact handoff from the genuine machine input to the actual logarithm
machine, with the original graph word protected in the archive. -/
def startInTime (n m : Nat) (rest : List Bool) :
    StateTransition.EvalsToInTime machine.step
      (initList machine (encodeWords [n, m] ++ rest))
      (some (clockConfiguration (startExtra rest (encodeWords [n, m] ++ rest)) none
        (initList MachineLogCounter.machine (encodeWord (n + m)))))
      (2 * ((encodeWords [n, m] ++ rest).length + 1) + 1 + (n + 1) + (m + 1)) := by
  let word := encodeWords [n, m] ++ rest
  let b₀ := startMemory word [] []
  let b₁ := startMemory word word []
  let b₂ := startMemory word word (encodeWord 0)
  have hc : Function.update b₀ (.inr .archive) (b₀ (.inr .input) ++ b₀ (.inr .archive)) = b₁ := by
    funext tape
    cases tape with
    | inl k => simp [b₀, b₁, startMemory]
    | inr k => cases k <;> simp [b₀, b₁, startMemory, startExtra]
  let copy := MachineCopy.copyInTime (.inr ExtraTape.input) (.inr ExtraTape.archive)
    (.inr ExtraTape.scratch) (by decide) (by decide) (by decide) false
    (.inr ExtraLabel.copyFirst) (.inr ExtraLabel.copySecond) (some (.inr ExtraLabel.seed))
    program rfl rfl b₀ rfl MachineLogCounter.initialState none
  have copy' : StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (.inr .copyFirst), initialState, b₀⟩
      (some ⟨some (.inr .seed), initialState, b₁⟩) (2 * (word.length + 1)) := by
    have h := copy
    rw [hc] at h
    simpa only [initialState, show b₀ (.inr .input) = word from rfl] using h
  have seed : StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (.inr .seed), initialState, b₁⟩
      (some ⟨some (.inr .headerFirst), initialState, b₂⟩) 1 := by
    refine ⟨⟨1, ?_⟩, le_rfl⟩
    change some (TM2.stepAux (program (.inr .seed)) initialState b₁) = _
    simp only [program, TM2.stepAux, b₁, startMemory]
    rw [startMemory_sum_update]
    rfl
  have first := headerInTime (.inr .headerFirst) (.inr .headerSecond) rfl
    n 0 (encodeWord m ++ rest) word MachineLogCounter.initialState none
  have first' : StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (.inr .headerFirst), initialState, b₂⟩
      (some ⟨some (.inr .headerSecond), initialState,
        startMemory (encodeWord m ++ rest) word (encodeWord n)⟩) (n + 1) := by
    simpa only [b₂, initialState, word, encodeWords, List.append_nil, List.append_assoc,
      Nat.add_zero] using first
  have second := headerInTime (.inr .headerSecond) (.inl 0) rfl
    m n rest word MachineLogCounter.initialState none
  have second' : StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (.inr .headerSecond), initialState,
        startMemory (encodeWord m ++ rest) word (encodeWord n)⟩
      (some ⟨some (.inl 0), initialState, startMemory rest word (encodeWord (n + m))⟩)
      (m + 1) := by simpa only [initialState, Nat.add_comm m n] using second
  let p₀ := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ copy' seed
  let p₁ := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ p₀ first'
  let p := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ p₁ second'
  rw [initialMemory, clockInitialMemory]
  exact {
    toEvalsTo := p.toEvalsTo
    steps_le_m := by
      have h := p.steps_le_m
      change p.steps ≤ 2 * (word.length + 1) + 1 + (n + 1) + (m + 1)
      omega
  }

end UniqueGamesTheorem.Foundations.Complexity.GraphCounterModel

/-! A complete finite machine adding the actual logarithmic graph-round count
as a unary prefix, preserving every bit of the original validated graph table. -/

namespace UniqueGamesTheorem.Foundations.Complexity.GraphCounterPrefix

open Turing PCP GraphCounterModel GraphCounterFinish

def rawOutput (n m : Nat) (rest : List Bool) : List Bool :=
  encodeWord ((n + m).log2 + 1) ++ (encodeWords [n, m] ++ rest)

def rawInTime (n m : Nat) (rest : List Bool) :
    TM2OutputsInTime machine (encodeWords [n, m] ++ rest) (some (rawOutput n m rest))
      (20 * (encodeWords [n, m] ++ rest).length + 30) := by
  let original := encodeWords [n, m] ++ rest
  let start := startInTime n m rest
  let clock := clockInTime (extraTapes rest original) none (n + m)
  let finish := finishInTime (encodeWord ((n + m).log2 + 1)) rest original
  have start' : StateTransition.EvalsToInTime (TM2.step program)
      (initList machine original)
      (some (clockConfiguration (extraTapes rest original) none
        (initList MachineLogCounter.machine (encodeWord (n + m)))))
      (2 * (original.length + 1) + 1 + (n + 1) + (m + 1)) := start
  let first := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ start' clock
  let total := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ first finish
  refine { toEvalsTo := total.toEvalsTo, steps_le_m := ?_ }
  have bound := total.steps_le_m
  have hlog := Nat.log2_le_self (n + m)
  have hlength : original.length = n + m + 2 + rest.length := by
    simp only [original, List.length_append, encodeWords, encodeWord_length, List.length_nil]
    omega
  simp only [encodeWord_length] at bound
  change total.steps ≤ 20 * original.length + 30
  omega

def count (table : GraphTables.Table) : Nat := (table.vertices + table.darts).log2 + 1

def output (table : GraphTables.Table) : List Bool :=
  encodeWord (count table) ++ GraphTables.tableBits table

def rowsBits (table : GraphTables.Table) : List Bool :=
  encodeWords ((GraphTables.rowList table).flatMap GraphTables.rowWords)

theorem tableBits_decomposition (table : GraphTables.Table) :
    GraphTables.tableBits table = encodeWords [table.vertices, table.darts] ++ rowsBits table :=
  encodeWords_append _ _

def outputsInTime (table : GraphTables.Table) :
    TM2OutputsInTime machine (GraphTables.tableBits table) (some (output table))
      (20 * (GraphTables.tableBits table).length + 30) := by
  have run := rawInTime table.vertices table.darts (rowsBits table)
  simpa only [rawOutput, output, count, tableBits_decomposition] using run

noncomputable def computableInPolyTime :
    TM2ComputableInPolyTime GraphTables.tableBits id output where
  tm := machine
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := 20 * Polynomial.X + 30
  outputsFun table := by
    change TM2OutputsInTime machine ((GraphTables.tableBits table).map id)
      (some ((output table).map id))
      ((20 * Polynomial.X + 30 : Polynomial Nat).eval (GraphTables.tableBits table).length)
    erw [List.map_id, List.map_id]
    simpa only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat,
      Polynomial.eval_X] using outputsInTime table

end UniqueGamesTheorem.Foundations.Complexity.GraphCounterPrefix

/-! Generic placement of the odometer-digit initialization used in
`Hastad.SourceLoopInit`. This extracts its seed/copy/trim scheme from the
formula/header parser: the actual checked copy loop preserves the radix and
scratch, and a single positive-unary pop leaves the remaining count.
The finite program depends on the fixed digit width, not on the radix value. -/

namespace UniqueGamesTheorem.Foundations.Complexity.MachineOdometerInit
open Turing

inductive Tape (k : Nat)
  | radix | scratch | current (j : Fin k) | remaining (j : Fin k)
  deriving DecidableEq, Fintype

inductive Label (k : Nat)
  | seed (j : Fin k) | copyOut (j : Fin k) | copyBack (j : Fin k) | trim (j : Fin k)
  | done
  deriving DecidableEq, Fintype

variable {k : Nat} {K Λ σ : Type} [DecidableEq K]

def labelAt (labels : Label k → Λ) (r : Nat) : Λ :=
  if h : r < k then labels (.seed ⟨r,h⟩) else labels .done

/-- Place one of finitely many actual statements into an arbitrary ambient
Boolean-tape program, preserving the ambient state component. -/
def statement (tape : Tape k → K) (labels : Label k → Λ) (exit : Option Λ) :
    Label k → TM2.Stmt (fun _ : K => Bool) Λ (σ × Option Bool)
  | .seed j => .push (tape (.current j)) (fun _ => false)
      (.goto (fun _ => labels (.copyOut j)))
  | .copyOut j => Reduction.MachineTransfer.loopAt (tape .radix) (tape .scratch)
      id false (labels (.copyOut j)) (some (labels (.copyBack j)))
  | .copyBack j => MachineCopy.forkLoop (tape .scratch) (tape .radix) (tape (.remaining j))
      false (labels (.copyBack j)) (some (labels (.trim j)))
  | .trim j => .pop (tape (.remaining j)) (fun state _ => state)
      (.goto (fun _ => labelAt labels (j.val+1)))
  | .done => .load (fun state => (state.1,none))
      (Reduction.MachineTransfer.exitAt (tape .radix) exit)

def digitOutput (tape : Tape k → K) (j : Fin k) (m : Nat) (base : K → List Bool) :
    K → List Bool :=
  Function.update (Function.update base (tape (.current j)) (encodeWord 0))
    (tape (.remaining j)) (encodeWord (m-1))

theorem digitOutput_frame (tape : Tape k → K) (j : Fin k) (m : Nat)
    (base : K → List Bool) (p : K) (hc : p ≠ tape (.current j))
    (hr : p ≠ tape (.remaining j)) : digitOutput tape j m base p = base p := by
  simp [digitOutput,hc,hr]

variable (tape : Tape k → K) (distinct : Function.Injective tape)
  (labels : Label k → Λ) (exit : Option Λ)
  (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ (σ × Option Bool))
  (atProgram : ∀l, program (labels l) = statement tape labels exit l)

def digitInTime (j : Fin k) (m : Nat) (hm : 0 < m) (base : K → List Bool)
    (hradix : base (tape .radix) = encodeWord m)
    (hcurrent : base (tape (.current j)) = [])
    (hremaining : base (tape (.remaining j)) = [])
    (hscratch : base (tape .scratch) = []) (ambient : σ) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (labels (.seed j)),(ambient,none),base⟩
      (some ⟨some (labelAt labels (j.val+1)),(ambient,none),digitOutput tape j m base⟩)
      (2*m+6) := by
  have hrc : tape .radix ≠ tape (.current j) := distinct.ne (by simp)
  have hrr : tape .radix ≠ tape (.remaining j) := distinct.ne (by simp)
  have hrs : tape .radix ≠ tape .scratch := distinct.ne (by simp)
  have hsc : tape .scratch ≠ tape (.current j) := distinct.ne (by simp)
  have hrsc : tape (.remaining j) ≠ tape .scratch := distinct.ne (by simp)
  have hrcc : tape (.remaining j) ≠ tape (.current j) := distinct.ne (by simp)
  let seeded := Function.update base (tape (.current j)) (encodeWord 0)
  have seedRun : StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (labels (.seed j)),(ambient,none),base⟩
      (some ⟨some (labels (.copyOut j)),(ambient,none),seeded⟩) 1 := by
    refine { steps := 1, evals_in_steps := ?_, steps_le_m := le_refl _ }
    change some (TM2.stepAux (program (labels (.seed j))) (ambient,none) base) = _
    rw [atProgram]
    simp [statement,TM2.stepAux,seeded,hcurrent,encodeWord]
  have copiedRun := MachineCopy.copyInTime (tape .radix) (tape (.remaining j)) (tape .scratch)
    hrr hrs hrsc false (labels (.copyOut j)) (labels (.copyBack j))
    (some (labels (.trim j))) program (atProgram (.copyOut j)) (atProgram (.copyBack j))
    seeded (by simpa [seeded,hsc] using hscratch) ambient none
  let copied := Function.update seeded (tape (.remaining j)) (encodeWord m)
  have he : Function.update seeded (tape (.remaining j))
      (seeded (tape .radix) ++ seeded (tape (.remaining j))) = copied := by
    simp [copied,seeded,hradix,hremaining,hrc,hrcc]
  rw [he] at copiedRun
  have trimRun : StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (labels (.trim j)),(ambient,none),copied⟩
      (some ⟨some (labelAt labels (j.val+1)),(ambient,none),digitOutput tape j m base⟩) 1 := by
    refine { steps := 1, evals_in_steps := ?_, steps_le_m := le_refl _ }
    change some (TM2.stepAux (program (labels (.trim j))) (ambient,none) copied) = _
    have hm' : m = (m-1)+1 := by omega
    have tail : (encodeWord m).tail = encodeWord (m-1) := by
      conv_lhs => rw [hm']
      simp [encodeWord,List.replicate_succ]
    rw [atProgram]
    simp [statement,TM2.stepAux,copied,seeded,digitOutput,tail]
  have joined := StateTransition.EvalsToInTime.trans (TM2.step program) _ _ _ _ _
    (StateTransition.EvalsToInTime.trans (TM2.step program) _ _ _ _ _ seedRun copiedRun) trimRun
  refine { steps := joined.steps, evals_in_steps := joined.evals_in_steps, steps_le_m := ?_ }
  apply Nat.le_trans joined.steps_le_m
  have hs : seeded (tape .radix) = encodeWord m := by simpa [seeded,hrc] using hradix
  rw [hs,encodeWord_length]
  omega

def stageTapes (tape : Tape k → K) (m : Nat) (base : K → List Bool) : Nat → K → List Bool
  | 0 => base
  | r+1 => if h : r < k then digitOutput tape ⟨r,h⟩ m (stageTapes tape m base r)
      else stageTapes tape m base r

theorem stageTapes_frame (m : Nat) (base : K → List Bool) (r : Nat)
    (p : K) (hc : ∀j, p ≠ tape (.current j)) (hr : ∀j, p ≠ tape (.remaining j)) :
    stageTapes tape m base r p = base p := by
  induction r with
  | zero => rfl
  | succ r ih =>
    simp only [stageTapes]
    split
    · rw [digitOutput_frame _ _ _ _ _ (hc _) (hr _),ih]
    · exact ih

include distinct in
theorem stageTapes_current (m : Nat) (base : K → List Bool) (r : Nat) (j : Fin k) :
    stageTapes tape m base r (tape (.current j)) =
      if j.val < r then encodeWord 0 else base (tape (.current j)) := by
  induction r with
  | zero => simp [stageTapes]
  | succ r ih =>
    simp only [stageTapes]
    split
    next hr =>
      by_cases hj : j = (⟨r,hr⟩ : Fin k)
      · subst j; simp [digitOutput,distinct.eq_iff]
      · rw [digitOutput_frame _ _ _ _ _
          (distinct.ne (by simpa using hj)) (distinct.ne (by simp)),ih]
        have hval : j.val ≠ r := by intro h; apply hj; exact Fin.ext h
        have he : j.val < r+1 ↔ j.val < r := by omega
        simp only [he]
    next hr =>
      rw [ih]
      have hjr : j.val < r := by omega
      have hjr' : j.val < r+1 := by omega
      simp only [hjr,hjr',ite_true]

include distinct in
theorem stageTapes_remaining (m : Nat) (base : K → List Bool) (r : Nat) (j : Fin k) :
    stageTapes tape m base r (tape (.remaining j)) =
      if j.val < r then encodeWord (m-1) else base (tape (.remaining j)) := by
  induction r with
  | zero => simp [stageTapes]
  | succ r ih =>
    simp only [stageTapes]
    split
    next hr =>
      by_cases hj : j = (⟨r,hr⟩ : Fin k)
      · subst j; simp [digitOutput]
      · rw [digitOutput_frame _ _ _ _ _
          (distinct.ne (by simp)) (distinct.ne (by simpa using hj)),ih]
        have hval : j.val ≠ r := by intro h; apply hj; exact Fin.ext h
        have he : j.val < r+1 ↔ j.val < r := by omega
        simp only [he]
    next hr =>
      rw [ih]
      have hjr : j.val < r := by omega
      have hjr' : j.val < r+1 := by omega
      simp only [hjr,hjr',ite_true]

/-- Place the actual finite initialization prefix inside an ambient program. -/
def prefixInTime (m : Nat) (hm : 0 < m) (base : K → List Bool)
    (hradix : base (tape .radix) = encodeWord m)
    (hcurrent : ∀j, base (tape (.current j)) = [])
    (hremaining : ∀j, base (tape (.remaining j)) = [])
    (hscratch : base (tape .scratch) = []) (ambient : σ) (r : Nat) (hr : r ≤ k) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (labelAt labels 0),(ambient,none),base⟩
      (some ⟨some (labelAt labels r),(ambient,none),stageTapes tape m base r⟩)
      (r*(2*m+6)) := by
  induction r with
  | zero => exact { steps := 0, evals_in_steps := rfl, steps_le_m := by omega }
  | succ r ih =>
    have hrk : r < k := by omega
    let j : Fin k := ⟨r,hrk⟩
    let before := stageTapes tape m base r
    have one := digitInTime tape distinct labels exit program atProgram j m hm before
      (by dsimp only [before]; rw [stageTapes_frame tape _ _ _ _
          (fun _ => distinct.ne (by simp)) (fun _ => distinct.ne (by simp))]; exact hradix)
      (by simp [before,stageTapes_current tape distinct,j,hcurrent])
      (by simp [before,stageTapes_remaining tape distinct,j,hremaining])
      (by dsimp only [before]; rw [stageTapes_frame tape _ _ _ _
          (fun _ => distinct.ne (by simp)) (fun _ => distinct.ne (by simp))]; exact hscratch)
      ambient
    have one' : StateTransition.EvalsToInTime (TM2.step program)
        ⟨some (labelAt labels r),(ambient,none),before⟩
        (some ⟨some (labelAt labels (r+1)),(ambient,none),stageTapes tape m base (r+1)⟩)
        (2*m+6) := by
      simpa only [labelAt,dite_eq_left hrk,j,stageTapes,before] using one
    have joined := StateTransition.EvalsToInTime.trans (TM2.step program) _ _ _ _ _
      (ih (by omega)) one'
    simpa only [Nat.add_mul,Nat.one_mul,Nat.add_comm] using joined

/-- Complete actual initialization, including width zero and the optional
continuation. The radix, scratch, ambient state and unrelated tapes survive. -/
def initializeInTime (m : Nat) (hm : 0 < m) (base : K → List Bool)
    (hradix : base (tape .radix) = encodeWord m)
    (hcurrent : ∀j, base (tape (.current j)) = [])
    (hremaining : ∀j, base (tape (.remaining j)) = [])
    (hscratch : base (tape .scratch) = []) (ambient : σ) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (labelAt labels 0),(ambient,none),base⟩
      (some ⟨exit,(ambient,none),stageTapes tape m base k⟩)
      (k*(2*m+6)+1) := by
  have initializedPrefix := prefixInTime tape distinct labels exit program atProgram m hm base
    hradix hcurrent hremaining hscratch ambient k (le_refl _)
  have doneRun : StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (labelAt labels k),(ambient,none),stageTapes tape m base k⟩
      (some ⟨exit,(ambient,none),stageTapes tape m base k⟩) 1 := by
    refine { steps := 1, evals_in_steps := ?_, steps_le_m := le_refl _ }
    change some (TM2.stepAux (program (labelAt labels k)) (ambient,none) _) = _
    simp only [labelAt,Nat.lt_irrefl,↓reduceDIte]
    rw [atProgram]
    cases exit <;> rfl
  simpa only [Nat.add_comm] using
    StateTransition.EvalsToInTime.trans (TM2.step program) _ _ _ _ _ initializedPrefix doneRun

include distinct in
theorem output_current (m : Nat) (base : K → List Bool) (j : Fin k) :
    stageTapes tape m base k (tape (.current j)) = encodeWord 0 := by
  rw [stageTapes_current tape distinct]
  exact ite_eq_left j.isLt

include distinct in
theorem output_remaining (m : Nat) (base : K → List Bool) (j : Fin k) :
    stageTapes tape m base k (tape (.remaining j)) = encodeWord (m-1) := by
  rw [stageTapes_remaining tape distinct]
  exact ite_eq_left j.isLt

include distinct in
theorem output_radix (m : Nat) (base : K → List Bool) :
    stageTapes tape m base k (tape .radix) = base (tape .radix) :=
  stageTapes_frame tape m base k _
    (fun _ => distinct.ne (by simp)) (fun _ => distinct.ne (by simp))

include distinct in
theorem output_scratch (m : Nat) (base : K → List Bool) :
    stageTapes tape m base k (tape .scratch) = base (tape .scratch) :=
  stageTapes_frame tape m base k _
    (fun _ => distinct.ne (by simp)) (fun _ => distinct.ne (by simp))

end UniqueGamesTheorem.Foundations.Complexity.MachineOdometerInit

namespace UniqueGamesTheorem.Foundations.Complexity.MachineRegisterEmit

open Turing
open UniqueGamesTheorem.Reduction.MachineSubstitution

variable {K Λ σ : Type} [DecidableEq K]

abbrev Alphabet (_ : K) := Bool

def finish (exit : Option Λ) : TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool) :=
  match exit with
  | none => .halt
  | some label => .goto fun _ => label

/-- The fixed literal push chain executes in one TM2 transition. -/
def emitStatement (destination : K) (offset : Nat) (exit : Option Λ) :
    TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool) :=
  pushWord destination (List.replicate offset true) (finish exit)

theorem emitStep (destination : K) (offset : Nat) (emitLabel : Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atEmit : program emitLabel = emitStatement destination offset exit)
    (base : K → List Bool) (ambient : σ) (register : Option Bool) :
    TM2.step program ⟨some emitLabel, (ambient, register), base⟩ =
      some ⟨exit, (ambient, register),
        Function.update base destination (List.replicate offset true ++ base destination)⟩ := by
  change some (TM2.stepAux (program emitLabel) (ambient, register) base) = _
  rw [atEmit, emitStatement, stepAux_pushWord]
  cases exit <;> simp [finish, TM2.stepAux]

theorem prefix_encodeWord (offset n : Nat) :
    List.replicate offset true ++ encodeWord n = encodeWord (offset + n) := by
  simp only [encodeWord, List.replicate_add, List.append_assoc]

/-- Caller-program form of the full exact trace. No execution premise is used. -/
theorem registerEmitTrace (source destination scratch : K)
    (sourceDestination : source ≠ destination) (sourceScratch : source ≠ scratch)
    (destinationScratch : destination ≠ scratch) (offset : Nat)
    (firstLabel secondLabel emitLabel : Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atFirst : program firstLabel =
      Reduction.MachineTransfer.loopAt source scratch id false firstLabel (some secondLabel))
    (atSecond : program secondLabel =
      MachineCopy.forkLoop scratch source destination false secondLabel (some emitLabel))
    (atEmit : program emitLabel = emitStatement destination offset exit)
    (base : K → List Bool) (n : Nat) (sourceWord : base source = encodeWord n)
    (scratchEmpty : base scratch = []) (ambient : σ) (register : Option Bool) :
    (MachineComposition.advance (TM2.step program))^[2 * n + 5]
      (some ⟨some firstLabel, (ambient, register), base⟩) =
      some ⟨exit, (ambient, none),
        Function.update base destination (encodeWord (offset + n) ++ base destination)⟩ := by
  have copied := MachineCopy.copyTrace source destination scratch sourceDestination
    sourceScratch destinationScratch false firstLabel secondLabel (some emitLabel)
    program atFirst atSecond base scratchEmpty ambient register
  rw [sourceWord, encodeWord_length] at copied
  rw [show 2 * n + 5 = 1 + 2 * (n + 1 + 1) by omega,
    Function.iterate_add_apply, copied, Function.iterate_one]
  change TM2.step program
    ⟨some emitLabel, (ambient, none),
      Function.update base destination (encodeWord n ++ base destination)⟩ = _
  rw [emitStep destination offset emitLabel exit program atEmit]
  simp only [Function.update_self, Function.update_idem]
  rw [← List.append_assoc, prefix_encodeWord]

/-- Timed witness retaining the exact `2*n+5`-transition execution. -/
def registerEmitInTime (source destination scratch : K)
    (sourceDestination : source ≠ destination) (sourceScratch : source ≠ scratch)
    (destinationScratch : destination ≠ scratch) (offset : Nat)
    (firstLabel secondLabel emitLabel : Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atFirst : program firstLabel =
      Reduction.MachineTransfer.loopAt source scratch id false firstLabel (some secondLabel))
    (atSecond : program secondLabel =
      MachineCopy.forkLoop scratch source destination false secondLabel (some emitLabel))
    (atEmit : program emitLabel = emitStatement destination offset exit)
    (base : K → List Bool) (n : Nat) (sourceWord : base source = encodeWord n)
    (scratchEmpty : base scratch = []) (ambient : σ) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some firstLabel, (ambient, register), base⟩
      (some ⟨exit, (ambient, none),
        Function.update base destination (encodeWord (offset + n) ++ base destination)⟩)
      (2 * n + 5) where
  steps := 2 * n + 5
  evals_in_steps := registerEmitTrace source destination scratch sourceDestination sourceScratch
    destinationScratch offset firstLabel secondLabel emitLabel exit program atFirst atSecond
    atEmit base n sourceWord scratchEmpty ambient register
  steps_le_m := Nat.le_refl _

/-- The three labels are transfer, restore-and-copy, and fixed-offset emission. -/
def program (source destination scratch : K) (offset : Nat) (exit : Option (Fin 3)) :
    Fin 3 → TM2.Stmt (Alphabet (K := K)) (Fin 3) (σ × Option Bool) :=
  fun label => if label = 0 then
    Reduction.MachineTransfer.loopAt source scratch id false 0 (some 1)
  else if label = 1 then
    MachineCopy.forkLoop scratch source destination false 1 (some 2)
  else emitStatement destination offset exit

def programInTime (source destination scratch : K)
    (sourceDestination : source ≠ destination) (sourceScratch : source ≠ scratch)
    (destinationScratch : destination ≠ scratch) (offset : Nat) (exit : Option (Fin 3))
    (base : K → List Bool) (n : Nat) (sourceWord : base source = encodeWord n)
    (scratchEmpty : base scratch = []) (ambient : σ) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step (program source destination scratch offset exit))
      ⟨some 0, (ambient, register), base⟩
      (some ⟨exit, (ambient, none),
        Function.update base destination (encodeWord (offset + n) ++ base destination)⟩)
      (2 * n + 5) :=
  registerEmitInTime source destination scratch sourceDestination sourceScratch
    destinationScratch offset 0 1 2 exit (program source destination scratch offset exit)
    (by simp [program]) (by simp [program]) (by simp [program])
    base n sourceWord scratchEmpty ambient register

/-- Three Boolean stacks, three labels, and one optional Boolean register. -/
def machine (offset : Nat) : FinTM2 where
  K := Fin 3
  k₀ := 0
  k₁ := 1
  Γ _ := Bool
  Λ := Fin 3
  main := 0
  σ := Unit × Option Bool
  initialState := ((), none)
  m := program 0 1 2 offset none

def machineInTime (offset : Nat) (base : Fin 3 → List Bool) (n : Nat)
    (sourceWord : base 0 = encodeWord n) (scratchEmpty : base 2 = [])
    (register : Option Bool) :
    StateTransition.EvalsToInTime (machine offset).step
      ⟨some (0 : Fin 3), ((), register), base⟩
      (some ⟨none, ((), none),
        Function.update base (1 : Fin 3) (encodeWord (offset + n) ++ base 1)⟩)
      (2 * n + 5) :=
  programInTime (0 : Fin 3) 1 2 (by decide) (by decide) (by decide)
    offset none base n sourceWord scratchEmpty () register

omit [DecidableEq K] in
theorem emitStatement_pushes (destination : K) (offset : Nat) (exit : Option Λ) :
    Runtime.statementPushBound (emitStatement (σ := σ) destination offset exit) = offset := by
  cases exit <;> simp [emitStatement, statementPushBound_pushWord, finish,
    Runtime.statementPushBound]

omit [DecidableEq K] in
theorem program_pushes_le (source destination scratch : K) (offset : Nat)
    (exit : Option (Fin 3)) (label : Fin 3) :
    Runtime.statementPushBound
      (program (σ := σ) source destination scratch offset exit label) ≤ max 2 offset := by
  unfold program
  split
  · simp [Reduction.MachineTransfer.loopAt, Reduction.MachineTransfer.exitAt,
      Runtime.statementPushBound]
  · split
    · simp [MachineCopy.forkLoop, Reduction.MachineTransfer.exitAt,
        Runtime.statementPushBound]
    · simpa only [emitStatement_pushes] using (Nat.le_max_right 2 offset)

/-- The fixed offset is included in the finite program's push bound. -/
theorem machine_pushes_le (offset : Nat) :
    Runtime.programPushBound (machine offset) ≤ max 2 offset := by
  have h : ∀ labels : List (Fin 3),
      Runtime.maxLabelPushes (machine offset).m labels ≤ max 2 offset := by
    intro labels
    change Runtime.maxLabelPushes (program (σ := Unit) (0 : Fin 3) 1 2 offset none)
      labels ≤ max 2 offset
    induction labels with
    | nil => exact Nat.zero_le _
    | cons label labels ih =>
      exact max_le (program_pushes_le (σ := Unit) (0 : Fin 3) 1 2 offset none label) ih
  exact h _

end UniqueGamesTheorem.Foundations.Complexity.MachineRegisterEmit

/-!
A concrete sequential composition of two finite TM2 programs. The first output
is transferred to a temporary stack and then to the second input. Both loops
execute actual transitions and reset their shared register on exit. Static
renaming changes neither a stack word nor the number of executed transitions.
-/

namespace UniqueGamesTheorem.Foundations.Complexity.MachineSequential

open Turing

abbrev Tape (first second : FinTM2) := first.K ⊕ (second.K ⊕ Unit)
abbrev Symbols (first second : FinTM2) : Tape first second → Type :=
  MachineEmbedding.Alphabet first.Γ
    (MachineEmbedding.Alphabet second.Γ (fun _ : Unit => second.Γ second.k₀))
abbrev Label (first second : FinTM2) := first.Λ ⊕ (Bool ⊕ second.Λ)
abbrev Register (second : FinTM2) := Option (second.Γ second.k₀)
abbrev State (first second : FinTM2) := (first.σ × second.σ) × Register second

def firstStates (first second : FinTM2) :
    first.σ × (second.σ × Register second) ≃ State first second where
  toFun st := ((st.1, st.2.1), st.2.2)
  invFun st := (st.1.1, (st.1.2, st.2))
  left_inv _ := rfl
  right_inv _ := rfl

def secondStates (first second : FinTM2) :
    second.σ × (first.σ × Register second) ≃ State first second where
  toFun st := ((st.2.1, st.1), st.2.2)
  invFun st := (st.1.2, (st.1.1, st.2))
  left_inv _ := rfl
  right_inv _ := rfl

def secondLabels (first second : FinTM2) :
    second.Λ ⊕ (Bool ⊕ first.Λ) → Label first second
  | .inl label => .inr (.inr label)
  | .inr (.inl bit) => .inr (.inl bit)
  | .inr (.inr label) => .inl label

def bridgeLabel (first second : FinTM2) (bit : Bool) : Label first second :=
  .inr (.inl bit)

def firstStatement (first second : FinTM2) (q : first.Stmt) :
    TM2.Stmt (Symbols first second) (Label first second) (State first second) :=
  MachineControl.statement id (firstStates first second)
    (MachineEmbedding.statement (some (bridgeLabel first second false)) q)

def secondStatement (first second : FinTM2) (q : second.Stmt) :
    TM2.Stmt (Symbols first second) (Label first second) (State first second) :=
  MachineControl.statement (secondLabels first second) (secondStates first second)
    (MachineStackSwap.statement
      (MachineEmbedding.statement
        (Δ := MachineEmbedding.Alphabet first.Γ (fun _ : Unit => second.Γ second.k₀))
        (Λextra := Bool ⊕ first.Λ) none q))

def program (first second : FinTM2)
    (relabel : first.Γ first.k₁ → second.Γ second.k₀)
    (fallback : second.Γ second.k₀) :
    Label first second → TM2.Stmt (Symbols first second) (Label first second)
      (State first second)
  | .inl label => firstStatement first second (first.m label)
  | .inr (.inr label) => secondStatement first second (second.m label)
  | .inr (.inl false) =>
      Reduction.MachineTransfer.loopAt (Γ := Symbols first second)
        (.inl first.k₁) (.inr (.inr ())) relabel fallback
        (bridgeLabel first second false) (some (bridgeLabel first second true))
  | .inr (.inl true) =>
      Reduction.MachineTransfer.loopAt (Γ := Symbols first second)
        (.inr (.inr ())) (.inr (.inl second.k₀)) id fallback
        (bridgeLabel first second true) (some (.inr (.inr second.main)))

def machine (first second : FinTM2)
    (relabel : first.Γ first.k₁ → second.Γ second.k₀)
    (fallback : second.Γ second.k₀) : FinTM2 where
  K := Tape first second
  kFin := by
    letI := first.kFin
    letI := second.kFin
    exact inferInstanceAs (Fintype (first.K ⊕ (second.K ⊕ Unit)))
  k₀ := .inl first.k₀
  k₁ := .inr (.inl second.k₁)
  Γ := Symbols first second
  Λ := Label first second
  ΛFin := by
    letI := first.ΛFin
    letI := second.ΛFin
    exact inferInstanceAs (Fintype (first.Λ ⊕ (Bool ⊕ second.Λ)))
  main := .inl first.main
  σ := State first second
  σFin := by
    letI := first.σFin
    letI := second.σFin
    letI := second.Γk₀Fin
    exact inferInstanceAs (Fintype ((first.σ × second.σ) × Option (second.Γ second.k₀)))
  initialState := ((first.initialState, second.initialState), none)
  Γk₀Fin := first.Γk₀Fin
  m := program first second relabel fallback

def firstConfiguration (first second : FinTM2) (c : first.Cfg) :
    TM2.Cfg (Symbols first second) (Label first second) (State first second) :=
  MachineControl.configuration id (firstStates first second)
    (MachineEmbedding.configuration (some (bridgeLabel first second false))
      (second.initialState, (none : Register second)) (fun _ => []) c)

def secondConfiguration (first second : FinTM2) (c : second.Cfg) :
    TM2.Cfg (Symbols first second) (Label first second) (State first second) :=
  MachineControl.configuration (secondLabels first second) (secondStates first second)
    (MachineStackSwap.configuration
      (MachineEmbedding.configuration
        (Δ := MachineEmbedding.Alphabet first.Γ (fun _ : Unit => second.Γ second.k₀))
        (Λextra := Bool ⊕ first.Λ) none
        (first.initialState, (none : Register second)) (fun _ => []) c))

theorem firstStep (first second : FinTM2)
    (relabel : first.Γ first.k₁ → second.Γ second.k₀)
    (fallback : second.Γ second.k₀) (a b : first.Cfg)
    (transition : first.step a = some b) :
    (machine first second relabel fallback).step (firstConfiguration first second a) =
      some (firstConfiguration first second b) := by
  cases a with
  | mk label state tapes =>
    cases label with
    | none => cases transition
    | some label =>
      have hb := Option.some.inj transition
      subst b
      change some (TM2.stepAux
        (MachineControl.statement id (firstStates first second)
          (MachineEmbedding.statement (some (bridgeLabel first second false)) (first.m label)))
        ((firstStates first second) (state, (second.initialState, none)))
        (MachineEmbedding.tapes tapes (fun _ => []))) = _
      have controlled := MachineControl.stepAux_simulation id (firstStates first second)
        (MachineEmbedding.statement
          (Δ := MachineEmbedding.Alphabet second.Γ (fun _ : Unit => second.Γ second.k₀))
          (some (bridgeLabel first second false)) (first.m label))
        (state, (second.initialState, none)) (MachineEmbedding.tapes tapes (fun _ => []))
      have embedded := MachineEmbedding.stepAux_simulation
        (Δ := MachineEmbedding.Alphabet second.Γ (fun _ : Unit => second.Γ second.k₀))
        (some (bridgeLabel first second false)) (second.initialState, (none : Register second))
        (fun _ => []) (first.m label) state tapes
      exact congrArg some (controlled.trans
        (congrArg (MachineControl.configuration id (firstStates first second)) embedded))

theorem secondStep (first second : FinTM2)
    (relabel : first.Γ first.k₁ → second.Γ second.k₀)
    (fallback : second.Γ second.k₀) (a b : second.Cfg)
    (transition : second.step a = some b) :
    (machine first second relabel fallback).step (secondConfiguration first second a) =
      some (secondConfiguration first second b) := by
  cases a with
  | mk label state tapes =>
    cases label with
    | none => cases transition
    | some label =>
      have hb := Option.some.inj transition
      subst b
      change some (TM2.stepAux
        (MachineControl.statement (secondLabels first second) (secondStates first second)
          (MachineStackSwap.statement
            (MachineEmbedding.statement
              (Δ := MachineEmbedding.Alphabet first.Γ (fun _ : Unit => second.Γ second.k₀))
              (Λextra := Bool ⊕ first.Λ) none (second.m label))))
        ((secondStates first second) (state, (first.initialState, none)))
        (MachineStackSwap.tapes (MachineEmbedding.tapes tapes (fun _ => [])))) = _
      rw [MachineControl.stepAux_simulation, MachineStackSwap.stepAux_simulation,
        MachineEmbedding.stepAux_simulation]
      rfl

theorem firstConfiguration_init (first second : FinTM2)
    (relabel : first.Γ first.k₁ → second.Γ second.k₀)
    (fallback : second.Γ second.k₀) (input : List (first.Γ first.k₀)) :
    firstConfiguration first second (initList first input) =
      initList (machine first second relabel fallback) input := by
  unfold firstConfiguration MachineControl.configuration MachineEmbedding.configuration initList
  congr 1
  funext k
  rcases k with k | k | k
  · by_cases h : k = first.k₀
    · subst k
      simp [machine, MachineEmbedding.tapes]
      rfl
    · simp [machine, MachineEmbedding.tapes, h]
  · simp [machine, MachineEmbedding.tapes]
  · simp [machine, MachineEmbedding.tapes]

theorem secondConfiguration_halt (first second : FinTM2)
    (relabel : first.Γ first.k₁ → second.Γ second.k₀)
    (fallback : second.Γ second.k₀) (output : List (second.Γ second.k₁)) :
    secondConfiguration first second (haltList second output) =
      haltList (machine first second relabel fallback) output := by
  unfold secondConfiguration MachineControl.configuration MachineStackSwap.configuration
    MachineEmbedding.configuration haltList
  congr 1
  funext k
  rcases k with k | k | k
  · simp [machine, MachineStackSwap.tapes, MachineEmbedding.tapes]
  · by_cases h : k = second.k₁
    · subst k
      simp [machine, MachineStackSwap.tapes, MachineEmbedding.tapes]
      rfl
    · simp [machine, MachineStackSwap.tapes, MachineEmbedding.tapes, h]
  · simp [machine, MachineStackSwap.tapes, MachineEmbedding.tapes]

def temporaryTapes (first second : FinTM2) (word : List (second.Γ second.k₀)) :
    ∀ k, List (Symbols first second k)
  | .inl _ => []
  | .inr (.inl _) => []
  | .inr (.inr _) => word

def temporaryConfiguration (first second : FinTM2) (word : List (second.Γ second.k₀)) :
    TM2.Cfg (Symbols first second) (Label first second) (State first second) :=
  ⟨some (bridgeLabel first second true),
    ((first.initialState, second.initialState), none), temporaryTapes first second word⟩

theorem firstTransfer_tapes (first second : FinTM2)
    (relabel : first.Γ first.k₁ → second.Γ second.k₀)
    (word : List (first.Γ first.k₁)) :
    Reduction.MachineTransfer.tapesAt (.inl first.k₁) (.inr (.inr ()))
      (firstConfiguration first second (haltList first word)).stk [] (word.reverse.map relabel) =
        temporaryTapes first second (word.reverse.map relabel) := by
  funext k
  rcases k with k | k | k
  · by_cases h : k = first.k₁
    · subst k
      simp [Reduction.MachineTransfer.tapesAt, temporaryTapes]
    · simp [Reduction.MachineTransfer.tapesAt, temporaryTapes, firstConfiguration,
        MachineControl.configuration, MachineEmbedding.configuration, MachineEmbedding.tapes,
        haltList, h]
  · simp [Reduction.MachineTransfer.tapesAt, temporaryTapes, firstConfiguration,
      MachineControl.configuration, MachineEmbedding.configuration, MachineEmbedding.tapes]
  · cases k
    simp [Reduction.MachineTransfer.tapesAt, temporaryTapes]

theorem secondTransfer_tapes (first second : FinTM2) (word : List (second.Γ second.k₀)) :
    Reduction.MachineTransfer.tapesAt (Γ := Symbols first second)
      (.inr (.inr ())) (.inr (.inl second.k₀))
      (temporaryTapes first second word) [] word.reverse =
        (secondConfiguration first second (initList second word.reverse)).stk := by
  funext k
  rcases k with k | k | k
  · simp [Reduction.MachineTransfer.tapesAt, temporaryTapes, secondConfiguration,
      MachineControl.configuration, MachineStackSwap.configuration, MachineStackSwap.tapes,
      MachineEmbedding.configuration, MachineEmbedding.tapes]
  · by_cases h : k = second.k₀
    · subst k
      simp [Reduction.MachineTransfer.tapesAt, secondConfiguration,
        MachineControl.configuration, MachineStackSwap.configuration, MachineStackSwap.tapes,
        MachineEmbedding.configuration, MachineEmbedding.tapes, initList]
    · simp [Reduction.MachineTransfer.tapesAt, temporaryTapes, secondConfiguration,
        MachineControl.configuration, MachineStackSwap.configuration, MachineStackSwap.tapes,
        MachineEmbedding.configuration, MachineEmbedding.tapes, initList, h]
  · cases k
    simp [Reduction.MachineTransfer.tapesAt, secondConfiguration,
      MachineControl.configuration, MachineStackSwap.configuration, MachineStackSwap.tapes,
      MachineEmbedding.configuration, MachineEmbedding.tapes]

def firstTransfer (first second : FinTM2)
    (relabel : first.Γ first.k₁ → second.Γ second.k₀)
    (fallback : second.Γ second.k₀) (word : List (first.Γ first.k₁)) :
    StateTransition.EvalsToInTime (machine first second relabel fallback).step
      (firstConfiguration first second (haltList first word))
      (some (temporaryConfiguration first second (word.reverse.map relabel)))
      (word.length + 1) := by
  let run := Reduction.MachineTransfer.transferAtInTime
    (.inl first.k₁ : Tape first second) (.inr (.inr ())) (by intro h; cases h)
    relabel fallback (bridgeLabel first second false)
    (some (bridgeLabel first second true)) (program first second relabel fallback) rfl
    (firstConfiguration first second (haltList first word)).stk
    (first.initialState, second.initialState) none
  have inputTape : (firstConfiguration first second (haltList first word)).stk (.inl first.k₁) =
      word := by simp [firstConfiguration, MachineControl.configuration,
        MachineEmbedding.configuration, MachineEmbedding.tapes, haltList]
  have outputTape :
      (firstConfiguration first second (haltList first word)).stk (.inr (.inr ())) = [] := rfl
  rw [inputTape, outputTape, List.append_nil, firstTransfer_tapes] at run
  exact run

def secondTransfer (first second : FinTM2)
    (relabel : first.Γ first.k₁ → second.Γ second.k₀)
    (fallback : second.Γ second.k₀) (word : List (second.Γ second.k₀)) :
    StateTransition.EvalsToInTime (machine first second relabel fallback).step
      (temporaryConfiguration first second word)
      (some (secondConfiguration first second (initList second word.reverse)))
      (word.length + 1) := by
  let run := Reduction.MachineTransfer.transferAtInTime
    (.inr (.inr ()) : Tape first second) (.inr (.inl second.k₀)) (by intro h; cases h)
    id fallback (bridgeLabel first second true) (some (.inr (.inr second.main)))
    (program first second relabel fallback) rfl (temporaryTapes first second word)
    (first.initialState, second.initialState) none
  simp only [temporaryTapes, List.map_id, List.append_nil] at run
  rw [secondTransfer_tapes] at run
  exact run

/-- An execution of each component yields an actual execution of the combined
machine. The two transfer loops add exactly twice the intermediate length plus two. -/
def execute (first second : FinTM2)
    (relabel : first.Γ first.k₁ → second.Γ second.k₀)
    (fallback : second.Γ second.k₀)
    (input : List (first.Γ first.k₀)) (middle : List (first.Γ first.k₁))
    (output : List (second.Γ second.k₁)) (firstBudget secondBudget : Nat)
    (runFirst : TM2OutputsInTime first input (some middle) firstBudget)
    (runSecond : TM2OutputsInTime second (middle.map relabel) (some output) secondBudget) :
    TM2OutputsInTime (machine first second relabel fallback) input (some output)
      (firstBudget + 2 * (middle.length + 1) + secondBudget) := by
  let start := MachineComposition.liftExecutionInTime first.step
    (machine first second relabel fallback).step (firstConfiguration first second)
    (firstStep first second relabel fallback) runFirst
  let bridge₁ := firstTransfer first second relabel fallback middle
  have bridge₂ := secondTransfer first second relabel fallback (middle.reverse.map relabel)
  have reversal : (middle.reverse.map relabel).reverse = middle.map relabel := by
    simp only [List.map_reverse, List.reverse_reverse]
  rw [reversal] at bridge₂
  simp only [List.length_map, List.length_reverse] at bridge₂
  let finish := MachineComposition.liftExecutionInTime second.step
    (machine first second relabel fallback).step (secondConfiguration first second)
    (secondStep first second relabel fallback) runSecond
  let phase₁₂ := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ start bridge₁
  let phase₁₂₃ := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ phase₁₂ bridge₂
  have full := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ phase₁₂₃ finish
  rw [firstConfiguration_init, secondConfiguration_halt] at full
  exact {
    toEvalsTo := full.toEvalsTo
    steps_le_m := by have h := full.steps_le_m; omega
  }

/-- General sequential composition with an explicit symbol of the intermediate
alphabet to totalize the bridge's unused empty-register expression. Its time
polynomial uses the transition-derived output-length bound of the first machine. -/
noncomputable def compose {α β γ αΓ βΓ γΓ : Type}
    {ea : α → List αΓ} {eb : β → List βΓ} {ec : γ → List γΓ}
    {f : α → β} {g : β → γ}
    (first : TM2ComputableInPolyTime ea eb f)
    (second : TM2ComputableInPolyTime eb ec g) (fallback : βΓ) :
    TM2ComputableInPolyTime ea ec (fun a => g (f a)) := by
  let relabel : first.tm.Γ first.tm.k₁ → second.tm.Γ second.tm.k₀ :=
    fun symbol => second.inputAlphabet.symm (first.outputAlphabet symbol)
  let defaultSymbol := second.inputAlphabet.symm fallback
  let intermediate : Polynomial Nat := Polynomial.X +
    Polynomial.C (Runtime.programPushBound first.tm) * first.time
  refine {
    tm := machine first.tm second.tm relabel defaultSymbol
    inputAlphabet := first.inputAlphabet
    outputAlphabet := second.outputAlphabet
    time := MachineComposition.compositionPolynomial first.time second.time intermediate
    outputsFun := ?_
  }
  intro a
  let input := (ea a).map first.inputAlphabet.invFun
  let middle := (eb (f a)).map first.outputAlphabet.invFun
  let output := (ec (g (f a))).map second.outputAlphabet.invFun
  have handoff : middle.map relabel = (eb (f a)).map second.inputAlphabet.invFun := by
    dsimp only [middle, relabel]
    simp only [List.map_map]
    apply List.map_congr_left
    intro symbol _
    exact congrArg second.inputAlphabet.symm (first.outputAlphabet.apply_symm_apply symbol)
  have runSecond : TM2OutputsInTime second.tm (middle.map relabel) (some output)
      (second.time.eval (eb (f a)).length) := by
    rw [handoff]
    exact second.outputsFun (f a)
  have full := execute first.tm second.tm relabel defaultSymbol input middle output
    (first.time.eval (ea a).length) (second.time.eval (eb (f a)).length)
    (first.outputsFun a) runSecond
  have intermediateBound : (eb (f a)).length ≤ intermediate.eval (ea a).length :=
    Runtime.encodedOutputLength first a
  have totalBound := MachineComposition.compositionBudget_le first.time second.time
    intermediate (ea a).length (eb (f a)).length intermediateBound
  have middleLength : middle.length = (eb (f a)).length := by simp only [middle, List.length_map]
  exact {
    toEvalsTo := full.toEvalsTo
    steps_le_m := by
      apply Nat.le_trans full.steps_le_m
      simpa only [middleLength] using totalBound
  }

noncomputable def composeBits {α β γ : Type}
    {ea : α → List Bool} {eb : β → List Bool} {ec : γ → List Bool}
    {f : α → β} {g : β → γ}
    (first : TM2ComputableInPolyTime ea eb f)
    (second : TM2ComputableInPolyTime eb ec g) :
    TM2ComputableInPolyTime ea ec (fun a => g (f a)) :=
  compose first second false

end UniqueGamesTheorem.Foundations.Complexity.MachineSequential

end OAI
