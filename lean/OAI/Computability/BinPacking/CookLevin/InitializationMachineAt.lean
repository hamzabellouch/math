import OAI.Computability.BinPacking.CookLevin.InitializationMachine
import OAI.Computability.BinPacking.CookLevin.ValidityMachine

namespace OAI

namespace BinPackingGames.Foundations.Complexity.CookLevin.InitializationMachineAt

open Turing PostfixModel
open Reduction.MachineSubstitution (pushWord stepAux_pushWord)
open InitializationMachine (Label termTokens bodySteps selectorSteps)

variable {K Λ σ : Type} [DecidableEq K]

abbrev Ports (K : Type) := Fin 6 ↪ K
abbrev Alphabet (_ : K) := Bool
abbrev State (σ : Type) := (σ × Bool) × Option Bool

def initialState (ambient : σ) : State σ := ((ambient, false), none)

def frame (p : Ports K) (base : K → List Bool) (contents : Fin 6 → List Bool)
    (k : K) : List Bool :=
  if k = p 0 then contents 0 else if k = p 1 then contents 1
  else if k = p 2 then contents 2 else if k = p 3 then contents 3
  else if k = p 4 then contents 4 else if k = p 5 then contents 5 else base k

@[simp] theorem frame_at (p : Ports K) (base : K → List Bool)
    (contents : Fin 6 → List Bool) (j : Fin 6) : frame p base contents (p j) = contents j := by
  fin_cases j <;> simp [frame, p.injective.eq_iff]

theorem frame_other (p : Ports K) (base : K → List Bool) (contents : Fin 6 → List Bool)
    (k : K) (hk : ∀ j, k ≠ p j) : frame p base contents k = base k := by
  simp [frame, hk]

theorem update_frame (p : Ports K) (base : K → List Bool) (contents : Fin 6 → List Bool)
    (j : Fin 6) (replacement : List Bool) :
    Function.update (frame p base contents) (p j) replacement =
      frame p base (Function.update contents j replacement) := by
  funext k
  by_cases hk : ∃ r, p r = k
  · obtain ⟨r, rfl⟩ := hk
    by_cases hr : r = j
    · subst r; simp
    · simp [p.injective.ne hr, hr]
  · have hn : ∀ r, k ≠ p r := fun r h => hk ⟨r, h.symm⟩
    simp [Function.update_of_ne (hn j), frame_other p base _ k hn]

def contents (m i d : Nat) (output count : List Bool) (j : Fin 6) : List Bool :=
  match j.val with
  | 0 => encodeWord m
  | 1 => encodeWord i
  | 2 => encodeWord d
  | 3 => []
  | 4 => output
  | _ => count

def tapes (p : Ports K) (base : K → List Bool) (m i d : Nat)
    (output count : List Bool) : K → List Bool := frame p base (contents m i d output count)

@[simp] theorem tapes_at (p : Ports K) (base : K → List Bool) (m i d : Nat)
    (output count : List Bool) (j : Fin 6) :
    tapes p base m i d output count (p j) = contents m i d output count j := by
  exact frame_at p base _ j

theorem tapes_other (p : Ports K) (base : K → List Bool) (m i d : Nat)
    (output count : List Bool) (k : K) (hk : ∀ j, k ≠ p j) :
    tapes p base m i d output count k = base k := frame_other p base _ k hk

theorem update_remaining (p : Ports K) (base : K → List Bool) (m i d r : Nat)
    (output count : List Bool) :
    Function.update (tapes p base m i d output count) (p 0) (encodeWord r) =
      tapes p base r i d output count := by
  rw [tapes, update_frame]
  congr 1
  funext j
  fin_cases j <;> simp [contents]

theorem update_current (p : Ports K) (base : K → List Bool) (m i d r : Nat)
    (output count : List Bool) :
    Function.update (tapes p base m i d output count) (p 1) (encodeWord r) =
      tapes p base m r d output count := by
  rw [tapes, update_frame]
  congr 1
  funext j
  fin_cases j <;> simp [contents]

theorem update_threshold (p : Ports K) (base : K → List Bool) (m i d r : Nat)
    (output count : List Bool) :
    Function.update (tapes p base m i d output count) (p 2) (encodeWord r) =
      tapes p base m i r output count := by
  rw [tapes, update_frame]
  congr 1
  funext j
  fin_cases j <;> simp [contents]

theorem update_reversed (p : Ports K) (base : K → List Bool) (m i d : Nat)
    (output count replacement : List Bool) :
    Function.update (tapes p base m i d output count) (p 4) replacement =
      tapes p base m i d replacement count := by
  rw [tapes, update_frame]
  congr 1
  funext j
  fin_cases j <;> simp [contents]

theorem update_count (p : Ports K) (base : K → List Bool) (m i d : Nat)
    (output count replacement : List Bool) :
    Function.update (tapes p base m i d output count) (p 5) replacement =
      tapes p base m i d output replacement := by
  rw [tapes, update_frame]
  congr 1
  funext j
  fin_cases j <;> simp [contents]

theorem push_current (p : Ports K) (base : K → List Bool) (m i d : Nat)
    (output count : List Bool) :
    Function.update (tapes p base m i d output count) (p 1) (true :: encodeWord i) =
      tapes p base m (i + 1) d output count := by
  rw [show true :: encodeWord i = encodeWord (i + 1) by
    simp [encodeWord, List.replicate_succ]]
  exact update_current p base m i d (i + 1) output count

def statement (p : Ports K) (label : Label ↪ Λ) : Label → TM2.Stmt (Alphabet (K := K)) Λ (State σ)
  | .guard => MachineUnaryCounter.guard (p 0) (label .inputTag) (label .done)
  | .inputTag => pushWord (p 4) (encodeWord 5) (.goto fun _ => label .scan)
  | .scan => MachineTransducerCopy.scanLoop (p 1) (p 3) false
      (fun _ b => label (.emit b)) (label .restore)
  | .emit b => MachineTransducerCopy.emitter (p 4) (fun _ _ => false)
      (fun _ symbol => [symbol]) (label .scan) false b
  | .restore => Reduction.MachineTransfer.loopAt (p 3) (p 1) id false
      (label .restore) (some (label .test))
  | .test => MachineUnaryCounter.guard (p 2) (label (.result false)) (label (.result true))
  | .result b => pushWord (p 4) (encodeWords [if b then 1 else 0, 3])
      (.push (p 5) (fun _ => true) (.push (p 5) (fun _ => true)
        (.push (p 5) (fun _ => true)
          (.push (p 1) (fun _ => true) (.goto fun _ => label .guard)))))
  | .done => .halt

def Agrees (p : Ports K) (label : Label ↪ Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ)) : Prop :=
  ∀ l, l ≠ .done → program (label l) = statement p label l

private theorem chain {α : Type*} {f : α → α} {x y z : α} {m n : Nat}
    (first : f^[m] x = y) (second : f^[n] y = z) : f^[m + n] x = z := by
  rw [Nat.add_comm m n, Function.iterate_add_apply, first, second]

theorem inputTagStep (p : Ports K) (label : Label ↪ Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ)) (ha : Agrees p label program)
    (base : K → List Bool) (m i d : Nat) (output count : List Bool) (ambient : σ) :
    TM2.step program ⟨some (label .inputTag), initialState ambient, tapes p base m i d output count⟩ =
      some ⟨some (label .scan), initialState ambient,
        tapes p base m i d ((encodeWord 5).reverse ++ output) count⟩ := by
  change some (TM2.stepAux (program (label .inputTag)) _ _) = _
  rw [ha .inputTag (by decide), statement, stepAux_pushWord]
  simp [TM2.stepAux, contents, update_reversed]

private theorem identity_output (control : Bool) (input : List Bool) :
    Reduction.MachineTransducer.output (fun (_ : Bool) _ => false)
      (fun _ symbol => [symbol]) control input = input := by
  induction input generalizing control with
  | nil => rfl
  | cons b input ih => simp [Reduction.MachineTransducer.output, ih]

theorem indexTrace (p : Ports K) (label : Label ↪ Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ)) (ha : Agrees p label program)
    (base : K → List Bool) (m i d : Nat) (output count : List Bool) (ambient : σ) :
    (MachineComposition.advance (TM2.step program))^[3 * (i + 1) + 2]
      (some ⟨some (label .scan), initialState ambient, tapes p base m i d output count⟩) =
      some ⟨some (label .test), initialState ambient,
        tapes p base m i d ((encodeWord i).reverse ++ output) count⟩ := by
  have h := MachineTransducerCopy.transduceCopyTrace (p 1) (p 3) (p 4)
    (p.injective.ne (by decide)) (p.injective.ne (by decide)) (p.injective.ne (by decide))
    false (fun _ _ => false) (fun _ symbol => [symbol])
    (label .scan) (label .restore) (fun _ b => label (.emit b)) (some (label .test)) program
    (ha .scan (by decide))
    (by intro control symbol; exact ha (.emit symbol) (by intro h; cases h))
    (ha .restore (by decide)) (tapes p base m i d output count)
    (by simp [contents]) ambient false none
  simpa [contents, identity_output, update_reversed, initialState] using h

theorem thresholdStep (p : Ports K) (label : Label ↪ Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ)) (ha : Agrees p label program)
    (base : K → List Bool) (m i d : Nat) (output count : List Bool) (ambient : σ) :
    TM2.step program ⟨some (label .test), initialState ambient, tapes p base m i d output count⟩ =
      some ⟨some (label (.result (decide (d = 0)))), initialState ambient,
        tapes p base m i (d - 1) output count⟩ := by
  change some (TM2.stepAux (program (label .test)) _ _) = _
  rw [ha .test (by decide)]
  cases d with
  | zero => simp [statement, MachineUnaryCounter.guard, TM2.stepAux, contents, initialState, encodeWord]
  | succ d =>
    simp only [statement, MachineUnaryCounter.guard, TM2.stepAux, initialState,
      tapes_at, contents, encodeWord, List.replicate_succ, List.cons_append]
    change some (⟨some (label (.result false)), initialState ambient,
      Function.update (tapes p base m i (d + 1) output count) (p 2) (encodeWord d)⟩ :
      TM2.Cfg (Alphabet (K := K)) Λ (State σ)) = _
    rw [update_threshold]
    simp [initialState]

theorem resultStep (p : Ports K) (label : Label ↪ Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ)) (ha : Agrees p label program)
    (base : K → List Bool) (m i d : Nat) (output count : List Bool) (ambient : σ) (b : Bool) :
    TM2.step program ⟨some (label (.result b)), initialState ambient, tapes p base m i d output count⟩ =
      some ⟨some (label .guard), initialState ambient, tapes p base m (i + 1) d
        ((encodeWords [if b then 1 else 0, 3]).reverse ++ output) (true :: true :: true :: count)⟩ := by
  change some (TM2.stepAux (program (label (.result b))) _ _) = _
  rw [ha (.result b) (by intro h; cases h), statement, stepAux_pushWord]
  simp [TM2.stepAux, contents, update_reversed, update_count, push_current]

theorem bodyTrace (p : Ports K) (label : Label ↪ Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ)) (ha : Agrees p label program)
    (base : K → List Bool) (m i d : Nat) (output count : List Bool) (ambient : σ) :
    (MachineComposition.advance (TM2.step program))^[bodySteps i]
      (some ⟨some (label .inputTag), initialState ambient, tapes p base m i d output count⟩) =
      some ⟨some (label .guard), initialState ambient, tapes p base m (i + 1) (d - 1)
        ((tokenBits (termTokens i d)).reverse ++ output) (true :: true :: true :: count)⟩ := by
  have tag : (MachineComposition.advance (TM2.step program))^[1]
      (some ⟨some (label .inputTag), initialState ambient, tapes p base m i d output count⟩) =
      some ⟨some (label .scan), initialState ambient,
        tapes p base m i d ((encodeWord 5).reverse ++ output) count⟩ := by
    simpa only [Function.iterate_one, MachineComposition.advance_some] using
      inputTagStep p label program ha base m i d output count ambient
  have index := indexTrace p label program ha base m i d
    ((encodeWord 5).reverse ++ output) count ambient
  let out := (encodeWord i).reverse ++ ((encodeWord 5).reverse ++ output)
  have test : (MachineComposition.advance (TM2.step program))^[1]
      (some ⟨some (label .test), initialState ambient, tapes p base m i d out count⟩) =
      some ⟨some (label (.result (decide (d = 0)))), initialState ambient,
        tapes p base m i (d - 1) out count⟩ := by
    simpa only [Function.iterate_one, MachineComposition.advance_some] using
      thresholdStep p label program ha base m i d out count ambient
  have result : (MachineComposition.advance (TM2.step program))^[1]
      (some ⟨some (label (.result (decide (d = 0)))), initialState ambient,
        tapes p base m i (d - 1) out count⟩) =
      some ⟨some (label .guard), initialState ambient, tapes p base m (i + 1) (d - 1)
        ((encodeWords [if decide (d = 0) then 1 else 0, 3]).reverse ++ out)
        (true :: true :: true :: count)⟩ := by
    simpa only [Function.iterate_one, MachineComposition.advance_some] using
      resultStep p label program ha base m i (d - 1) out count ambient (decide (d = 0))
  have whole := chain (chain (chain tag index) test) result
  have ht : 1 + (3 * (i + 1) + 2) + 1 + 1 = bodySteps i := by
    unfold InitializationMachine.bodySteps
    omega
  rw [ht] at whole
  simpa only [InitializationMachine.termTokens_bits, List.reverse_append,
    List.append_assoc, out] using whole

theorem guardStep_zero (p : Ports K) (label : Label ↪ Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ)) (ha : Agrees p label program)
    (base : K → List Bool) (i d : Nat) (output count : List Bool) (ambient : σ) :
    TM2.step program ⟨some (label .guard), initialState ambient, tapes p base 0 i d output count⟩ =
      some ⟨some (label .done), initialState ambient, tapes p base 0 i d output count⟩ := by
  change some (TM2.stepAux (program (label .guard)) _ _) = _
  rw [ha .guard (by decide)]
  simp [statement, MachineUnaryCounter.guard, TM2.stepAux, contents, initialState, encodeWord]

theorem guardStep_succ (p : Ports K) (label : Label ↪ Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ)) (ha : Agrees p label program)
    (base : K → List Bool) (m i d : Nat) (output count : List Bool) (ambient : σ) :
    TM2.step program ⟨some (label .guard), initialState ambient, tapes p base (m + 1) i d output count⟩ =
      some ⟨some (label .inputTag), initialState ambient, tapes p base m i d output count⟩ := by
  change some (TM2.stepAux (program (label .guard)) _ _) = _
  rw [ha .guard (by decide)]
  simp only [statement, MachineUnaryCounter.guard, TM2.stepAux, initialState,
    tapes_at, contents, encodeWord, List.replicate_succ, List.cons_append]
  change some (⟨some (label .inputTag), initialState ambient,
    Function.update (tapes p base (m + 1) i d output count) (p 0) (encodeWord m)⟩ :
    TM2.Cfg (Alphabet (K := K)) Λ (State σ)) = _
  rw [update_remaining]
  rfl

theorem prepend_three (n : Nat) (count : List Bool) :
    List.replicate n true ++ (true :: true :: true :: count) =
      List.replicate (n + 3) true ++ count := by
  change List.replicate n true ++ (List.replicate 3 true ++ count) = _
  rw [← List.append_assoc, List.replicate_append_replicate]

theorem selectorTrace (p : Ports K) (label : Label ↪ Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ)) (ha : Agrees p label program)
    (base : K → List Bool) (m i d : Nat) (output count : List Bool) (ambient : σ) :
    (MachineComposition.advance (TM2.step program))^[selectorSteps i m]
      (some ⟨some (label .guard), initialState ambient, tapes p base m i d output count⟩) =
      some ⟨some (label .done), initialState ambient, tapes p base 0 (i + m) (d - m)
        ((tokenBits (InitializationTemplate.selectorLoopTokens m i d)).reverse ++ output)
        (List.replicate (3 * m) true ++ count)⟩ := by
  induction m generalizing i d output count with
  | zero =>
    simpa only [InitializationMachine.selectorSteps, InitializationTemplate.selectorLoopTokens,
      InitializationTemplate.forTokens, tokenBits, tokenWords, List.flatMap_nil,
      encodeWords, List.reverse_nil, List.nil_append, Nat.add_zero, Nat.sub_zero,
      Nat.mul_zero, List.replicate_zero, Function.iterate_one, MachineComposition.advance_some] using
      guardStep_zero p label program ha base i d output count ambient
  | succ m ih =>
    have guard : (MachineComposition.advance (TM2.step program))^[1]
        (some ⟨some (label .guard), initialState ambient, tapes p base (m + 1) i d output count⟩) =
        some ⟨some (label .inputTag), initialState ambient, tapes p base m i d output count⟩ := by
      simpa only [Function.iterate_one, MachineComposition.advance_some] using
        guardStep_succ p label program ha base m i d output count ambient
    have body := bodyTrace p label program ha base m i d output count ambient
    have rest := ih (i + 1) (d - 1) ((tokenBits (termTokens i d)).reverse ++ output)
      (true :: true :: true :: count)
    have whole := chain (chain guard body) rest
    rw [prepend_three] at whole
    have hs : InitializationTemplate.selectorLoopTokens (m + 1) i d =
        termTokens i d ++ InitializationTemplate.selectorLoopTokens m (i + 1) (d - 1) :=
      InitializationTemplate.selectorLoopTokens_succ m i d
    rw [hs, InitializationMachine.tokens_append_bits, List.reverse_append, List.append_assoc]
    simpa only [InitializationMachine.selectorSteps, Nat.add_assoc, Nat.add_comm,
      Nat.add_left_comm, Nat.sub_sub, Nat.mul_succ] using whole

def selectorInTime (p : Ports K) (label : Label ↪ Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ)) (ha : Agrees p label program)
    (base : K → List Bool) (m i d : Nat) (output count : List Bool) (ambient : σ) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (label .guard), initialState ambient, tapes p base m i d output count⟩
      (some ⟨some (label .done), initialState ambient, tapes p base 0 (i + m) (d - m)
        ((tokenBits (InitializationTemplate.selectorLoopTokens m i d)).reverse ++ output)
        (List.replicate (3 * m) true ++ count)⟩)
      (m * (3 * (i + m) + 6) + 1) where
  steps := selectorSteps i m
  evals_in_steps := selectorTrace p label program ha base m i d output count ambient
  steps_le_m := InitializationMachine.selectorSteps_le i m

theorem increment_count (m c : Nat) (suffix : List Bool) :
    List.replicate (3 * m) true ++ (encodeWord c ++ suffix) =
      encodeWord (c + 3 * m) ++ suffix := by
  simp only [encodeWord, ← List.append_assoc, List.replicate_append_replicate]
  rw [Nat.add_comm (3 * m) c]

omit [DecidableEq K] in
theorem standalone_agrees (p : Ports K) :
    Agrees (σ := σ) p (Function.Embedding.refl Label)
      (statement p (Function.Embedding.refl Label)) := by
  intro l _
  rfl

def machine [Fintype K] [Fintype σ] (p : Ports K) (ambient : σ) : FinTM2 where
  K := K
  k₀ := p 0
  k₁ := p 4
  Γ _ := Bool
  Λ := Label
  main := .guard
  σ := State σ
  initialState := initialState ambient
  m := statement p (Function.Embedding.refl Label)

def closurePorts (p : Ports K) (closing : K) (hc : ∀ j, closing ≠ p j) : OrClosure.Ports K where
  remaining := closing
  reversed := p 4
  count := p 5
  remaining_ne_reversed := hc 4
  remaining_ne_count := hc 5
  reversed_ne_count := p.injective.ne (by decide)

theorem presenceTrace (p : Ports K) (label : Label ↪ Λ)
    (closing : K) (hc : ∀ j, closing ≠ p j) (again : Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ)) (ha : Agrees p label program)
    (atSeed : program (label .done) = OrClosure.seed (closurePorts p closing hc) again)
    (atLoop : program again = OrClosure.loop (closurePorts p closing hc) again exit)
    (base : K → List Bool) (q n : Nat) (suffix output count : List Bool)
    (hclosing : base closing = encodeWord (q + 1) ++ suffix) (ambient : σ) :
    let selected := tapes p base 0 (q + 1) (n + 1 - (q + 1))
      ((tokenBits (InitializationTemplate.selectorLoopTokens (q + 1) 0 (n + 1))).reverse ++ output)
      (List.replicate (3 * (q + 1)) true ++ count)
    (MachineComposition.advance (TM2.step program))^[selectorSteps 0 (q + 1) + (q + 1 + 2)]
      (some ⟨some (label .guard), initialState ambient, tapes p base (q + 1) 0 (n + 1) output count⟩) =
      some ⟨exit, initialState ambient,
        OrClosure.frame (closurePorts p closing hc) selected (encodeWord 0 ++ suffix)
          ((tokenBits (InitializationTemplate.presenceTokens q n)).reverse ++ output)
          (List.replicate (4 * (q + 1) + 1) true ++ count)⟩ := by
  dsimp only
  let out := (tokenBits (InitializationTemplate.selectorLoopTokens (q + 1) 0 (n + 1))).reverse ++ output
  let cnt := List.replicate (3 * (q + 1)) true ++ count
  let selected := tapes p base 0 (q + 1) (n + 1 - (q + 1)) out cnt
  have hs := selectorTrace p label program ha base (q + 1) 0 (n + 1) output count ambient
  simp only [Nat.zero_add] at hs
  have hr : selected closing = encodeWord (q + 1) ++ suffix :=
    (tapes_other p base _ _ _ out cnt closing hc).trans hclosing
  have ho : selected (p 4) = out := by simp [selected, contents]
  have hn : selected (p 5) = cnt := by simp [selected, contents]
  have hf : OrClosure.frame (closurePorts p closing hc) selected
      (encodeWord (q + 1) ++ suffix) out cnt = selected := by
    simpa only [closurePorts, hr, ho, hn] using
      OrClosure.frame_self (closurePorts p closing hc) selected
  have hclose := OrClosure.closureTrace (closurePorts p closing hc) (label .done) again exit
    program atSeed atLoop selected (q + 1) suffix out cnt (ambient, false) none
  rw [hf] at hclose
  have whole := chain hs hclose
  have hout : (tokenBits (InitializationTemplate.closeOr (q + 1))).reverse ++ out =
      (tokenBits (InitializationTemplate.presenceTokens q n)).reverse ++ output := by
    rw [← InitializationTemplate.selectorLoopTokens_presence q n,
      InitializationMachine.tokens_append_bits, List.reverse_append, List.append_assoc]
  have hcnt : List.replicate (q + 1 + 1) true ++ cnt =
      List.replicate (4 * (q + 1) + 1) true ++ count := by
    dsimp only [cnt]
    rw [← List.append_assoc, List.replicate_append_replicate]
    congr 2
    omega
  rw [hout, hcnt] at whole
  exact whole

theorem presenceSteps_le (q : Nat) :
    selectorSteps 0 (q + 1) + (q + 1 + 2) ≤
      (q + 1) * (3 * (q + 1) + 7) + 3 := by
  have h := InitializationMachine.selectorSteps_le 0 (q + 1)
  simp only [Nat.zero_add] at h
  rw [show 3 * (q + 1) + 7 = (3 * (q + 1) + 6) + 1 by omega,
    Nat.mul_add, Nat.mul_one]
  omega

theorem presence_count (q c : Nat) (suffix : List Bool) :
    List.replicate (4 * (q + 1) + 1) true ++ (encodeWord c ++ suffix) =
      encodeWord (c + (4 * (q + 1) + 1)) ++ suffix := by
  simp only [encodeWord, ← List.append_assoc, List.replicate_append_replicate]
  rw [Nat.add_comm (4 * (q + 1) + 1) c]

end BinPackingGames.Foundations.Complexity.CookLevin.InitializationMachineAt

end OAI
